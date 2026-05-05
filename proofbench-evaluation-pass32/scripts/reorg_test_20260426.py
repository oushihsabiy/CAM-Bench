#!/usr/bin/env python3
import json
import os
import re
from pathlib import Path


SRC_ROOT = Path(__file__).resolve().parents[1] / "data-pair" / "test_20260426_235712"
INFORMAL_DIR = SRC_ROOT / "informal"
TARGET_ROOT = Path(__file__).resolve().parents[1] / "proof-bench" / "problems" / "test_20260426_235712"


def find_json_entry(chapter_json_path, lean_base):
    if not chapter_json_path.exists():
        return None
    try:
        data = json.loads(chapter_json_path.read_text(encoding='utf-8'))
    except Exception:
        return None

    # extract numeric parts from lean_base e.g. Exercise_3_17__a_ -> [3,17]
    nums = re.findall(r"(\d+)", lean_base)
    candidates = []
    if len(nums) >= 2:
        major, minor = nums[0], nums[1]
        candidates.append(f"Exercise {major}.{minor}")
        candidates.append(f"Exercise {major} {minor}")
        candidates.append(f"Exercise {major}.{minor}-")
    # also try simple contains of lean_base with underscores replaced
    candidates.append(lean_base.replace('_', ' '))
    candidates.append(lean_base)

    for entry in data:
        text = ' '.join(str(entry.get(k, '')).lower() for k in ('source_idx', 'problem', 'source'))
        for c in candidates:
            if c.lower() in text:
                return entry
    return None


def main():
    print("SRC_ROOT:", SRC_ROOT)
    print("INFORMAL_DIR:", INFORMAL_DIR)
    print("TARGET_ROOT:", TARGET_ROOT)

    if not SRC_ROOT.exists():
        print("Source root not found", SRC_ROOT)
        return

    TARGET_ROOT.mkdir(parents=True, exist_ok=True)

    lean_files = list(SRC_ROOT.rglob("*.lean"))
    print(f"Found {len(lean_files)} lean files")

    processed = 0
    missing = []

    for lean_path in lean_files:
        # skip the informal folder jsons
        if INFORMAL_DIR in lean_path.parents:
            continue
        rel = lean_path.relative_to(SRC_ROOT)
        chapter = rel.parts[0]
        lean_base = lean_path.stem

        chapter_json = INFORMAL_DIR / f"{chapter}.json"

        entry = find_json_entry(chapter_json, lean_base)

        # create target dir: TARGET_ROOT/chapter/Exercise_xxx/
        dest_dir = TARGET_ROOT / chapter / lean_base
        dest_dir.mkdir(parents=True, exist_ok=True)

        # copy lean to formal.lean
        formal_dst = dest_dir / "formal.lean"
        formal_dst.write_text(lean_path.read_text(encoding='utf-8'), encoding='utf-8')

        if entry is not None:
            informal_dst = dest_dir / "informal.json"
            # write the single json entry
            informal_dst.write_text(json.dumps(entry, ensure_ascii=False, indent=2), encoding='utf-8')
        else:
            missing.append(str(rel))

        processed += 1

    print(f"Processed: {processed}, missing json for: {len(missing)} files")
    if missing:
        print("Missing examples (first 20):")
        for m in missing[:20]:
            print(" -", m)


if __name__ == '__main__':
    main()
