# Informal Evaluation Task Generation

Generate `informal_evaluation/eval/task.json` from one or more chapter JSON files:

```bash
cd /root/workspace/benchmark/informal_evaluation
python -m eval.generate_task.generate --config eval/generate_task/config.json
python -m eval.run_eval --config eval/task.json --parallel 4
```

`models` can be either strings that inherit the top-level `api_key`/`base_url`, or
objects with per-model credentials:

```json
{
  "models": [
    {
      "model": "model-a",
      "api_key": "sk-a",
      "base_url": "https://provider-a.example.com/v1"
    },
    {
      "model": "model-b",
      "api_key": "sk-b",
      "base_url": "https://provider-b.example.com/v1"
    }
  ]
}
```

To run only selected models from an existing `task.json`:

```bash
python -m eval.run_eval --config eval/task.json --model model-a
python -m eval.run_eval --config eval/task.json --models model-a,model-b
```

Use `input_dirs` to generate tasks from every JSON file under one or more directories
recursively:

```json
{
  "input_dirs": ["/path/to/chapter_json_dir"],
  "input_glob": "*.json"
}
```

`input_files` and the legacy single `input_dir` key are still accepted for compatibility.
Each input JSON may be a top-level list, `{ "blocks": [...] }`, or `{ "problems": [...] }`.
Each block must contain a `problem` or `statement` field. Existing `proof` and
`direct_answer` fields are preserved in `problem.json` output but are not included in
the model prompt.
