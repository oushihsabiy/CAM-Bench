#!/usr/bin/env python3
"""Submit and inspect Aristotle proving jobs.

Examples:
  ARISTOTLE_API_KEY=arstl_... python scripts/aristotle_request.py submit \
    --project-dir . \
    --prompt "Prove the theorem in formal.lean by replacing the final sorry."

  ARISTOTLE_API_KEY=arstl_... python scripts/aristotle_request.py status PROJECT_ID

  ARISTOTLE_API_KEY=arstl_... python scripts/aristotle_request.py download PROJECT_ID \
    --destination result.tar.gz

  ARISTOTLE_API_KEY=arstl_... python scripts/aristotle_request.py cancel PROJECT_ID
"""

from __future__ import annotations

import argparse
import asyncio
import json
from pathlib import Path

import aristotlelib
from aristotlelib import Project


def project_to_dict(project: Project) -> dict[str, object]:
    return {
        "project_id": project.project_id,
        "status": project.status.value,
        "percent_complete": project.percent_complete,
        "created_at": project.created_at.isoformat(),
        "last_updated_at": project.last_updated_at.isoformat(),
        "file_name": project.file_name,
        "description": project.description,
        "output_summary": project.output_summary,
    }


def print_project(project: Project) -> None:
    print(json.dumps(project_to_dict(project), indent=2, ensure_ascii=False))


async def submit(args: argparse.Namespace) -> None:
    project = await Project.create_from_directory(
        prompt=args.prompt,
        project_dir=args.project_dir,
    )
    print_project(project)

    if args.wait:
        result = await project.wait_for_completion(destination=args.destination)
        if result is not None:
            print(json.dumps({"downloaded": result}, indent=2))


async def status(args: argparse.Namespace) -> None:
    project = await Project.from_id(args.project_id)
    print_project(project)


async def download(args: argparse.Namespace) -> None:
    project = await Project.from_id(args.project_id)
    print_project(project)
    result = await project.get_solution_if_complete(destination=args.destination)
    print(json.dumps({"downloaded": result}, indent=2))


async def cancel(args: argparse.Namespace) -> None:
    project = await Project.from_id(args.project_id)
    await project.cancel()
    print_project(project)


async def main(args: argparse.Namespace) -> None:
    if args.api_key:
        aristotlelib.set_api_key(args.api_key)
    await args.func(args)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Submit/query Aristotle API jobs via aristotlelib.")
    parser.add_argument(
        "--api-key",
        help="Aristotle API key. Prefer ARISTOTLE_API_KEY instead of putting secrets in shell history.",
    )

    subparsers = parser.add_subparsers(dest="command", required=True)

    submit_parser = subparsers.add_parser("submit", help="Submit a Lean project directory.")
    submit_parser.add_argument(
        "--project-dir",
        type=Path,
        default=Path.cwd(),
        help="Lean project directory to upload. Default: current working directory.",
    )
    submit_parser.add_argument(
        "--prompt",
        required=True,
        help="Instructions for Aristotle.",
    )
    submit_parser.add_argument(
        "--wait",
        action="store_true",
        help="Wait for completion and download the result if finished.",
    )
    submit_parser.add_argument(
        "--destination",
        type=Path,
        help="Where to save the result archive when --wait is used.",
    )
    submit_parser.set_defaults(func=submit)

    status_parser = subparsers.add_parser("status", help="Print current project status.")
    status_parser.add_argument("project_id")
    status_parser.set_defaults(func=status)

    download_parser = subparsers.add_parser("download", help="Download result if the project is complete.")
    download_parser.add_argument("project_id")
    download_parser.add_argument(
        "--destination",
        type=Path,
        help="Where to save the result archive.",
    )
    download_parser.set_defaults(func=download)

    cancel_parser = subparsers.add_parser("cancel", help="Cancel a queued or running project.")
    cancel_parser.add_argument("project_id")
    cancel_parser.set_defaults(func=cancel)

    return parser


if __name__ == "__main__":
    asyncio.run(main(build_parser().parse_args()))
