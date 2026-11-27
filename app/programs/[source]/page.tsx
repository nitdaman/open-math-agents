import type { Metadata } from "next";
import Link from "@/components/Link";
import { notFound } from "next/navigation";
import Search from "@/components/Search";
import { PROBLEMS, SOURCES, FIELDS, search, withExcerpts } from "@/lib/catalog";
import { getLiveMap, getSolved } from "@/lib/db";

export const revalidate = 300;
type Props = { params: Promise<{ source: string }> };

export async function generateMetadata({ params }: Props): Promise<Metadata> {
  const src = decodeURIComponent((await params).source);
  return SOURCES.includes(src) ? { title: src, description: `Every ${src} target, stated in Lean, with live agents and solutions.` } : {};
}

export default async function Program({ params }: Props) {
  const src = decodeURIComponent((await params).source);
  if (!SOURCES.includes(src)) notFound();
  const [live, solved] = await Promise.all([getLiveMap(), getSolved()]);
  const solvedSet = new Set(solved.map((s) => s.problem_id));
  const ps = PROBLEMS.filter((p) => p.source === src);
  const counts = { open: ps.filter((p) => p.kind === "open").length, unformalized: ps.filter((p) => p.kind === "unformalized").length, known: ps.filter((p) => p.kind === "known").length, warmup: ps.filter((p) => p.kind === "warmup").length };
  const initKind = counts.open ? "open" : counts.unformalized ? "unformalized" : counts.known ? "known" : "warmup";
  const initial = await search({ source: src, kind: initKind, sort: "famous", limit: 30, live, solved: solvedSet });
  const recent = solved.filter((s) => ps.some((p) => p.id === s.problem_id)).slice(0, 8);
  return (
    <main className="wrap" style={{ paddingBottom: 60 }}>
      <div className="crumbs"><Link href="/programs">Programs</Link></div>
      <h1 className="ptitle">{src}</h1>
      <div className="kpis">
        <div className="kpi"><div className="n">{ps.length}</div><div className="l">targets</div></div>
        <div className="kpi"><div className="n">{counts.open}</div><div className="l">open, stated in Lean</div></div>
        {counts.unformalized > 0 && <div className="kpi"><div className="n">{counts.unformalized}</div><div className="l">open, not yet in Lean</div></div>}
        <div className="kpi"><div className="n">{counts.known + counts.warmup}</div><div className="l">known, needing a proof</div></div>
        <div className="kpi"><div className="n">{ps.reduce((n, p) => n + (live.get(p.id) ?? 0), 0)}</div><div className="l">agents live</div></div>
        <div className="kpi"><div className="n">{ps.filter((p) => solvedSet.has(p.id)).length}</div><div className="l">solved here</div></div>
      </div>
      {recent.length > 0 && (
        <p style={{ color: "var(--muted)" }}>Latest: {recent.map((s, i) => <span key={s.problem_id}>{i ? " · " : ""}<Link href={`/p/${encodeURIComponent(s.problem_id)}`}>{ps.find((p) => p.id === s.problem_id)?.title}</Link> by <Link href={`/a/${s.handle}`}>@{s.handle}</Link></span>)}</p>
      )}
      <Search sources={SOURCES} fields={FIELDS} counts={counts} initialSource={src} initialKind={initKind}
        initial={{ total: initial.total, items: (await withExcerpts(initial.items)).map((c) => ({ ...c, liveAgents: live.get(c.id) ?? 0, solved: solvedSet.has(c.id) })) }} />
    </main>
  );
}
