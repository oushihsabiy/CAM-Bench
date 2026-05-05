from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from eval.generate_task.generate import generate_tasks
from eval.problem_loader import load_chapter
from eval.run_eval import build_messages, filter_tasks_by_model, parse_model_filter, run_one_task
from eval.task_manager import completed_keys_from_output, load_tasks, prune_task_file, task_completion_key


class InformalEvalTests(unittest.TestCase):
    def test_loader_accepts_list_blocks_and_problems(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            list_path = root / "list.json"
            blocks_path = root / "blocks.json"
            problems_path = root / "problems.json"
            list_path.write_text(json.dumps([{"index": 1, "problem": "Show A."}]), encoding="utf-8")
            blocks_path.write_text(json.dumps({"blocks": [{"statement": "Show B."}]}), encoding="utf-8")
            problems_path.write_text(json.dumps({"problems": [{"problem": "Show C."}]}), encoding="utf-8")

            self.assertEqual(load_chapter(list_path)[0].problem_text, "Show A.")
            self.assertEqual(load_chapter(blocks_path)[0].problem_text, "Show B.")
            self.assertEqual(load_chapter(problems_path)[0].problem_text, "Show C.")

    def test_generate_tasks_from_chapter_json(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            chapter = root / "chapter.json"
            chapter.write_text(
                json.dumps([{"source_idx": "Exercise 1.1", "problem": "Prove X.", "proof": "hidden"}]),
                encoding="utf-8",
            )
            tasks = generate_tasks(
                {
                    "base_url": "http://localhost/v1",
                    "api_key": "EMPTY",
                    "models": ["m1", "m2"],
                    "input_files": [str(chapter)],
                    "pass_n": 3,
                    "output_root": str(root / "results"),
                }
            )
            self.assertEqual(len(tasks), 2)
            self.assertEqual(tasks[0]["pass_n"], 3)
            self.assertEqual(tasks[0]["problem_id"], "Exercise 1.1")
            self.assertEqual(tasks[0]["block"]["proof"], "hidden")

    def test_generate_tasks_reads_all_json_files_from_input_dirs(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_dir = root / "chapters"
            nested_dir = input_dir / "nested" / "deeper"
            nested_dir.mkdir(parents=True)
            (input_dir / "a.json").write_text(json.dumps([{"problem": "Prove A."}]), encoding="utf-8")
            (nested_dir / "b.json").write_text(json.dumps([{"problem": "Prove B."}]), encoding="utf-8")
            (input_dir / "ignore.txt").write_text("not json", encoding="utf-8")

            tasks = generate_tasks(
                {
                    "base_url": "http://localhost/v1",
                    "api_key": "EMPTY",
                    "models": ["m1"],
                    "input_dirs": [str(input_dir)],
                    "output_root": str(root / "results"),
                }
            )
            self.assertEqual(len(tasks), 2)
            self.assertEqual([task["chapter_stem"] for task in tasks], ["a", "b"])

    def test_generate_tasks_allows_per_model_credentials(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            chapter = root / "chapter.json"
            chapter.write_text(json.dumps([{"problem": "Prove X."}]), encoding="utf-8")
            tasks = generate_tasks(
                {
                    "base_url": "http://default/v1",
                    "api_key": "default-key",
                    "models": [
                        {
                            "model": "m1",
                            "base_url": "http://m1/v1",
                            "api_key": "m1-key",
                            "max_tokens_per_call": 111,
                            "llm_retry_initial_delay": 0.5,
                        },
                        "m2",
                    ],
                    "input_files": [str(chapter)],
                    "output_root": str(root / "results"),
                    "llm_retry_initial_delay": 2,
                    "llm_retry_max_delay": 30,
                }
            )
            by_model = {task["model"]: task for task in tasks}
            self.assertEqual(by_model["m1"]["base_url"], "http://m1/v1")
            self.assertEqual(by_model["m1"]["api_key"], "m1-key")
            self.assertEqual(by_model["m1"]["max_tokens_per_call"], 111)
            self.assertEqual(by_model["m1"]["llm_retry_initial_delay"], 0.5)
            self.assertEqual(by_model["m1"]["llm_retry_max_delay"], 30)
            self.assertEqual(by_model["m2"]["base_url"], "http://default/v1")
            self.assertEqual(by_model["m2"]["api_key"], "default-key")
            self.assertEqual(by_model["m2"]["llm_retry_initial_delay"], 2)

    def test_model_filter_helpers(self) -> None:
        selected = parse_model_filter(["m1,m2", "m3"])
        self.assertEqual(selected, {"m1", "m2", "m3"})
        tasks = [{"model": "m1"}, {"model": "m2"}, {"model": "m4"}]
        self.assertEqual(filter_tasks_by_model(tasks, selected), [{"model": "m1"}, {"model": "m2"}])
        self.assertEqual(filter_tasks_by_model(tasks, set()), tasks)

    def test_prompt_does_not_include_reference_proof_fields(self) -> None:
        task = {
            "source": "book",
            "source_idx": "Exercise 1.1",
            "problem": "Prove X.",
            "block": {
                "problem": "Prove X.",
                "proof": "REFERENCE_PROOF_SHOULD_NOT_APPEAR",
                "direct_answer": "REFERENCE_ANSWER_SHOULD_NOT_APPEAR",
                "题目类型": ["证明题"],
            },
        }
        prompt = "\n".join(message["content"] for message in build_messages(task))
        self.assertIn("Prove X.", prompt)
        self.assertNotIn("REFERENCE_PROOF_SHOULD_NOT_APPEAR", prompt)
        self.assertNotIn("REFERENCE_ANSWER_SHOULD_NOT_APPEAR", prompt)

    def test_successful_generation_writes_outputs_and_prunes_task(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            task = {
                "chapter_path": str(root / "chapter.json"),
                "chapter_stem": "chapter",
                "problem_id": "Exercise 1.1",
                "problem_slug": "Exercise_1_1",
                "source_idx": "Exercise 1.1",
                "source": "book",
                "problem": "Prove X.",
                "block": {"problem": "Prove X.", "proof": "hidden"},
                "model": "mock-model",
                "base_url": "http://localhost/v1",
                "api_key": "EMPTY",
                "pass_n": 3,
                "max_tokens_per_call": 100,
                "problem_timeout": 1,
            }
            task_path = root / "task.json"
            task_path.write_text(json.dumps([task]), encoding="utf-8")

            with mock.patch("eval.run_eval.generate_with_usage") as mocked:
                mocked.return_value = (
                    "Proof text.",
                    type("Usage", (), {"prompt_tokens": 1, "completion_tokens": 2, "total_tokens": 3})(),
                )
                summary = run_one_task(task, root / "results" / "run")

            self.assertTrue(summary["generated_at_n"])
            out_dir = Path(summary["output_dir"])
            self.assertTrue((out_dir / "problem.json").exists())
            self.assertTrue((out_dir / "proof_pass_001.md").exists())
            self.assertEqual(mocked.call_count, 3)

            keys = completed_keys_from_output(root / "results")
            before, removed, after = prune_task_file(task_path, keys)
            self.assertEqual((before, removed, after), (1, 1, 0))
            self.assertEqual(load_tasks(task_path), [])
            self.assertTrue(task_path.with_suffix(".json.bak").exists())

    def test_same_problem_slug_different_chapter_paths_do_not_share_output_dir(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            chapter_a = root / "book_a" / "Ch2" / "Exercise_2_2" / "informal.json"
            chapter_b = root / "book_b" / "Ch2" / "Exercise_2_2" / "informal.json"
            chapter_a.parent.mkdir(parents=True)
            chapter_b.parent.mkdir(parents=True)
            chapter_a.write_text(json.dumps({"problem": "Prove A."}), encoding="utf-8")
            chapter_b.write_text(json.dumps({"problem": "Prove B."}), encoding="utf-8")
            base_task = {
                "chapter_stem": "informal",
                "problem_id": "Exercise 2.2",
                "problem_slug": "Exercise_2.2",
                "model": "mock-model",
                "base_url": "http://localhost/v1",
                "pass_n": 1,
                "llm_retry_initial_delay": 0,
            }
            task_a = {**base_task, "chapter_path": str(chapter_a), "problem": "Prove A."}
            task_b = {**base_task, "chapter_path": str(chapter_b), "problem": "Prove B."}

            with mock.patch("eval.run_eval.generate_with_usage") as mocked:
                mocked.return_value = (
                    "Proof text.",
                    type("Usage", (), {"prompt_tokens": 1, "completion_tokens": 2, "total_tokens": 3})(),
                )
                summary_a = run_one_task(task_a, root / "results" / "run")
                summary_b = run_one_task(task_b, root / "results" / "run")

            self.assertNotEqual(summary_a["output_dir"], summary_b["output_dir"])
            self.assertTrue((Path(summary_a["output_dir"]) / "proof_pass_001.md").exists())
            self.assertTrue((Path(summary_b["output_dir"]) / "proof_pass_001.md").exists())

    def test_failed_generation_keeps_task(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            task = {
                "chapter_path": str(root / "chapter.json"),
                "chapter_stem": "chapter",
                "problem_id": "Exercise 1.2",
                "problem_slug": "Exercise_1_2",
                "problem": "Prove Y.",
                "model": "mock-model",
                "base_url": "http://localhost/v1",
                "pass_n": 1,
                "llm_retry_max_attempts": 1,
            }
            task_path = root / "task.json"
            task_path.write_text(json.dumps([task]), encoding="utf-8")

            with mock.patch("eval.run_eval.generate_with_usage", side_effect=RuntimeError("boom")):
                summary = run_one_task(task, root / "results" / "run")

            self.assertFalse(summary["generated_at_n"])
            keys = completed_keys_from_output(root / "results")
            self.assertFalse(keys)
            before, removed, after = prune_task_file(task_path, keys)
            self.assertEqual((before, removed, after), (1, 0, 1))
            self.assertEqual(task_completion_key(load_tasks(task_path)[0]), task_completion_key(task))

    def test_llm_errors_retry_until_successful_proof(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            task = {
                "chapter_path": str(root / "chapter.json"),
                "chapter_stem": "chapter",
                "problem_id": "Exercise 1.3",
                "problem_slug": "Exercise_1_3",
                "problem": "Prove Z.",
                "model": "mock-model",
                "base_url": "http://localhost/v1",
                "pass_n": 1,
                "llm_retry_initial_delay": 0,
            }

            usage = type("Usage", (), {"prompt_tokens": 4, "completion_tokens": 5, "total_tokens": 9})()
            with mock.patch(
                "eval.run_eval.generate_with_usage",
                side_effect=[
                    RuntimeError("LLM API error 429: Too many pending requests"),
                    RuntimeError("LLM API error 429: Concurrency limit exceeded"),
                    ("Proof after retry.", usage),
                ],
            ) as mocked:
                summary = run_one_task(task, root / "results" / "run")

            self.assertTrue(summary["generated_at_n"])
            self.assertEqual(mocked.call_count, 3)
            self.assertEqual([a["status"] for a in summary["attempts"]], ["error", "error", "success"])
            self.assertEqual([a["retry_index"] for a in summary["attempts"]], [1, 2, 3])
            proof_file = Path(summary["output_dir"]) / "proof_pass_001.md"
            self.assertEqual(proof_file.read_text(encoding="utf-8"), "Proof after retry.\n")


if __name__ == "__main__":
    unittest.main()
