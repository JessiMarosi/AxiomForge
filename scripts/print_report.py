#!/usr/bin/env python3
import argparse
from pathlib import Path
from reportlab.lib.pagesizes import letter
from reportlab.pdfgen import canvas

def sanitize(name: str) -> str:
    out = []
    for ch in name:
        if ch.isalnum() or ch in "._+-":
            out.append(ch)
        else:
            out.append("_")
    s = "".join(out).strip("_")
    return s or "project"

def read_steps(project_dir: Path):
    log = project_dir / 'steps.log'
    if not log.exists():
        return []
    lines = log.read_text(encoding='utf-8').splitlines()
    steps = []
    for line in lines:
        if '|' in line:
            n, msg = line.split('|', 1)
            steps.append((n.strip(), msg.strip()))
    return steps

def read_notes(root: Path):
    notes = root / 'NOTES.md'
    if not notes.exists():
        return []
    lines = notes.read_text(encoding='utf-8').splitlines()
    phases = [ln for ln in lines if ln.startswith('## Phase ')]
    return phases[-120:]

def read_dashboard_artifacts(project_dir: Path):
    artifacts_dir = project_dir / 'artifacts'
    if not artifacts_dir.exists():
        return []
    files = sorted(artifacts_dir.glob('dashboard_*.txt'))
    out = []
    for f in files:
        out.append((f.name, f.read_text(encoding='utf-8')))
    return out

def draw_wrapped(c, x, y, text, max_width, line_height):
    words = text.split()
    if not words:
        c.drawString(x, y, ' ')
        return y - line_height
    line = ''
    for w in words:
        candidate = (line + ' ' + w).strip()
        if c.stringWidth(candidate, 'Times-Roman', 10) <= max_width:
            line = candidate
        else:
            c.drawString(x, y, line)
            y -= line_height
            line = w
    if line:
        c.drawString(x, y, line)
        y -= line_height
    return y

def new_page(c, height, margin):
    c.showPage()
    return height - margin

def heading(c, x, y, title):
    c.setFont('Times-Bold', 12)
    c.drawString(x, y, title)
    return y - 16

def subheading(c, x, y, title):
    c.setFont('Times-Bold', 10)
    c.drawString(x, y, title)
    return y - 14

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--project', required=True)
    ap.add_argument('--out', required=True)
    args = ap.parse_args()

    root = Path(__file__).resolve().parent.parent
    proj_id = sanitize(args.project)
    proj_dir = root / 'projects' / proj_id

    steps = read_steps(proj_dir)
    phases = read_notes(root)
    artifacts = read_dashboard_artifacts(proj_dir)

    outpath = Path(args.out).expanduser()
    outpath.parent.mkdir(parents=True, exist_ok=True)

    c = canvas.Canvas(str(outpath), pagesize=letter)
    width, height = letter
    margin = 54
    x = margin
    y = height - margin

    # Cover / Header
    c.setFont('Times-Bold', 16)
    c.drawString(x, y, 'Axiom Forge — Project Report')
    y -= 22
    c.setFont('Times-Roman', 12)
    c.drawString(x, y, f'Project name: {args.project}')
    y -= 16
    c.drawString(x, y, f'Project id: {proj_id}')
    y -= 22

    # Table of Contents (deterministic)
    y = heading(c, x, y, 'Table of Contents')
    c.setFont('Times-Roman', 10)
    toc = []
    toc.append('1. Recorded Steps')
    toc.append('2. Dashboard Outputs')
    if artifacts:
        for i, (fname, _) in enumerate(artifacts, start=1):
            toc.append(f'   2.{i} {fname}')
    toc.append('3. Repo Phase Summary (NOTES.md)')
    for line in toc:
        y = draw_wrapped(c, x, y, line, max_width=width - 2*margin, line_height=12)
        if y < margin + 72:
            y = new_page(c, height, margin)

    # Hard page break after TOC
    y = new_page(c, height, margin)

    # Section 1: Steps
    y = heading(c, x, y, '1. Recorded Steps (deterministic order)')
    c.setFont('Times-Roman', 10)
    for n, msg in steps:
        y = draw_wrapped(c, x, y, f'{n}. {msg}', max_width=width - 2*margin, line_height=12)
        if y < margin + 72:
            y = new_page(c, height, margin)

    # Hard page break before dashboard section
    y = new_page(c, height, margin)

    # Section 2: Dashboard outputs
    y = heading(c, x, y, '2. Dashboard Outputs (captured stdout)')
    c.setFont('Times-Roman', 10)
    if not artifacts:
        y = draw_wrapped(c, x, y, '(no dashboard outputs captured for this project)', max_width=width - 2*margin, line_height=12)
    else:
        for i, (fname, body) in enumerate(artifacts, start=1):
            # Page break per captured dashboard output (user-friendly)
            y = subheading(c, x, y, f'2.{i} {fname}')
            c.setFont('Times-Roman', 10)
            for raw in body.splitlines():
                line = raw.rstrip('\n')
                # Add lightweight labels when present (still deterministic)
                if line.startswith('OFFICIAL OUTPUT') or line.startswith('LAYMAN'):
                    c.setFont('Times-Bold', 10)
                    y = draw_wrapped(c, x, y, line, max_width=width - 2*margin, line_height=12)
                    c.setFont('Times-Roman', 10)
                else:
                    y = draw_wrapped(c, x, y, line if line.strip() else ' ', max_width=width - 2*margin, line_height=12)
                if y < margin + 72:
                    y = new_page(c, height, margin)
            # Hard page break after each dashboard output block
            y = new_page(c, height, margin)

    # Section 3: NOTES summary
    y = heading(c, x, y, '3. Repo Phase Summary (from NOTES.md)')
    c.setFont('Times-Roman', 10)
    for ln in phases:
        y = draw_wrapped(c, x, y, ln, max_width=width - 2*margin, line_height=12)
        if y < margin + 72:
            y = new_page(c, height, margin)

    c.showPage()
    c.save()

if __name__ == '__main__':
    main()
