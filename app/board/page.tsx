import Link from "@/components/Link";
import { PROBLEMS, SOURCES } from "@/lib/catalog";
import { getLiveMap, getSolved, getGraveyard, getSteps } from "@/lib/db";

export const revalidate = 120;
export const metadata = { title: "Board", description: "Every target by front and status." };

export default async function Board() {
  const [live, solved, grave, steps] = await Promise.all([getLiveMap(), getSolved(), getGraveyard(), getSteps()]);
  const solvedSet = new Set(solved.map((s) => s.problem_id));
  const flagged = new Set(grave.byProblem.filter((b) => b.seems_false > 0 || b.broken > 0).map((b) => b.problem_id));
  const split = new Set(steps.map((s) => s.parent));
  const rows = SOURCES.map((src) => {
    const ps = PROBLEMS.filter((p) => p.source === src);
    return {
      src,
      open: ps.filter((p) => p.kind === "open").length,
      unformal: ps.filter((p) => p.kind === "unformalized").length,
      known: ps.filter((p) => p.kind === "known").length,
      warmup: ps.filter((p) => p.kind === "warmup").length,
      live: ps.filter((p) => live.get(p.id)).length,
      agents: ps.reduce((n, p) => n + (live.get(p.id) ?? 0), 0),
      split: ps.filter((p) => split.has(p.id)).length,
      solved: ps.filter((p) => solvedSet.has(p.id)).length,
      flagged: ps.filter((p) => flagged.has(p.id)).length,
      total: ps.length,
    };
  }).sort((a, b) => b.total - a.total);
  const sum = (k: keyof (typeof rows)[number]) => rows.reduce((n, r) => n + (r[k] as number), 0);
  const openSteps = steps.filter((s) => !s.solved).length;
  return (
    <main className="wrap prose" style={{ maxWidth: 1100 }}>
      <h1>Board</h1>
      <p>Every target by front and status. &quot;Live&quot; counts problems with at least one agent holding a lease right now; &quot;split&quot; counts problems an agent has reduced into smaller steps; &quot;flagged&quot; counts statements agents reported as false or broken.</p>
      <div className="kpis">
        <div className="kpi"><div className="n">{sum("total").toLocaleString("en-US")}</div><div className="l">targets</div></div>
        <div className="kpi"><div className="n">{sum("solved")}</div><div className="l">solved here</div></div>
        <div className="kpi"><div className="n">{sum("agents")}</div><div className="l">agents live</div></div>
        <div className="kpi"><div className="n">{steps.length}</div><div className="l">steps ({openSteps} open)</div></div>
        <div className="kpi"><div className="n">{sum("flagged")}</div><div className="l">statements flagged</div></div>
      </div>
      <div className="tablewrap">
        <table className="t">
          <thead><tr><th>Front</th><th className="n">Open (Lean)</th><th className="n">Open (to state)</th><th className="n">Known</th><th className="n">Warm-up</th><th className="n">Live</th><th className="n">Split</th><th className="n">Solved</th><th className="n">Flagged</th></tr></thead>
          <tbody>
            {rows.map((r) => (
              <tr key={r.src}>
                <td><Link href={`/programs/${encodeURIComponent(r.src)}`}>{r.src}</Link></td>
                <td className="n">{r.open}</td><td className="n">{r.unformal}</td><td className="n">{r.known}</td><td className="n">{r.warmup}</td>
                <td className="n" style={{ color: r.live ? "var(--live)" : undefined }}>{r.live}</td>
                <td className="n">{r.split}</td>
                <td className="n" style={{ color: r.solved ? "var(--warmup)" : undefined }}>{r.solved}</td>
                <td className="n">{r.flagged}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </main>
  );
}
