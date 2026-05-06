#!/usr/bin/env python3
"""Translate Chinese math problem JSON to English, preserving LaTeX exactly.

Usage:
    python scripts/translate_chinese_data.py data/最优化建模理论与方法.json \
        --config config2.json \
        --output data/最优化建模理论与方法_en.json

Resumes automatically: already-translated entries (detected by _translated=true)
are skipped so you can re-run safely after interruption.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

# Make sure project src is importable
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from json2lean.config.api_client import APIClient

TRANSLATE_PROMPT = """\
You are a precise mathematical translator. Translate the following Chinese math exercise problem text into English.

Rules:
1. Preserve ALL LaTeX math expressions EXACTLY as-is — do not alter any symbols, commands, or formatting inside \\(...\\), \\[...\\], $...$, $$...$$, or LaTeX environments.
2. Translate only the Chinese natural-language text surrounding the math.
3. Use standard mathematical English phrasing (e.g. "Prove that", "Let", "Show that", "Suppose", "Define").
4. Do not add, remove, or reorder any mathematical content.
5. Do not add explanations or commentary outside the translated text.
6. Output ONLY the translated text, nothing else — no JSON wrapper, no markdown fences.

Chinese text to translate:
"""


def load_config(config_path: str) -> dict:
    with open(config_path, encoding="utf-8") as f:
        return json.load(f)


def build_client(cfg: dict) -> APIClient:
    return APIClient(
        api_key=cfg["api_key"],
        base_url=cfg["base_url"],
        model=cfg["model"],
    )


def translate_one(client: APIClient, text: str, label: str) -> str:
    prompt = TRANSLATE_PROMPT + text
    for attempt in range(4):
        try:
            result = client.chat(
                prompt=prompt,
                max_tokens=4096,
                call_type="translate_chinese",
                exercise_label=label,
                json_mode=False,
            )
            return result.strip()
        except Exception as e:
            wait = 2 ** attempt
            print(f"  [warn] attempt {attempt+1} failed: {e}, retrying in {wait}s...", file=sys.stderr)
            time.sleep(wait)
    raise RuntimeError(f"Translation failed for {label} after 4 attempts")


def main() -> None:
    parser = argparse.ArgumentParser(description="Translate Chinese math JSON to English")
    parser.add_argument("input", help="Input JSON file (Chinese)")
    parser.add_argument("--config", default="config2.json", help="API config file")
    parser.add_argument("--output", help="Output JSON file (default: input stem + _en.json)")
    parser.add_argument("--resume", action="store_true", default=True,
                        help="Skip already-translated entries (default: on)")
    args = parser.parse_args()

    input_path = Path(args.input)
    if args.output:
        output_path = Path(args.output)
    else:
        output_path = input_path.parent / (input_path.stem + "_en.json")

    cfg = load_config(args.config)
    client = build_client(cfg)

    with open(input_path, encoding="utf-8") as f:
        data = json.load(f)

    # Load existing output for resume
    translated: list = []
    translated_indices: set = set()
    if output_path.exists() and args.resume:
        with open(output_path, encoding="utf-8") as f:
            translated = json.load(f)
        translated_indices = {item["index"] for item in translated}
        print(f"[resume] {len(translated_indices)} entries already translated", file=sys.stderr)

    total = len(data)
    for item in data:
        idx = item["index"]
        label = f"{item.get('source_idx', idx)}"

        if idx in translated_indices:
            print(f"[skip] [{idx}/{total}] {label}", file=sys.stderr)
            continue

        print(f"[translate] [{idx}/{total}] {label} ...", file=sys.stderr)
        new_item = dict(item)

        problem_zh = item.get("problem", "")
        if problem_zh:
            en = translate_one(client, problem_zh, label)
            new_item["problem"] = en
            new_item["problem_zh"] = problem_zh  # preserve original
        else:
            print(f"  [warn] no problem field, skipping", file=sys.stderr)

        new_item["_translated"] = True
        translated.append(new_item)

        # Save after every entry (safe resume)
        with open(output_path, "w", encoding="utf-8") as f:
            json.dump(translated, f, ensure_ascii=False, indent=2)

        print(f"  [done] saved to {output_path}", file=sys.stderr)

    print(f"\n[finished] {len(translated)} entries -> {output_path}", file=sys.stderr)


if __name__ == "__main__":
    main()
