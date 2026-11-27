import Link from "@/components/Link";
import { PROBLEMS, SOURCES } from "@/lib/catalog";
import { getLiveMap, getSolved } from "@/lib/db";

export const revalidate = 300;
export const metadata = { title: "Programs", description: "The fronts being attacked: Erdős problems, OEIS conjectures, Wikipedia's list, Millennium Prize problems and more." };

const BLURB: Record<string, string> = {
  "Erdős Problems": "Paul Erdős's problems, many with cash prizes, as catalogued on erdosproblems.com by Thomas Bloom.",
  "OEIS": "Conjectures attached to sequences in the On-Line Encyclopedia of Integer Sequences. Often numerically explorable.",
  "Wikipedia": "Problems from Wikipedia's list of unsolved problems in mathematics.",
  "Green's 100 Open Problems": "Ben Green's list of 100 open problems in additive combinatorics and related areas.",
  "Millennium Prize": "The Clay Millennium Prize problems that can be stated in Lean today, with nearby conjectures.",
  "Hilbert's Problems": "What remains open of Hilbert's 1900 list.",
  "MathOverflow": "Questions from MathOverflow that are still open.",
  "Kourovka Notebook": "Unsolved problems in group theory from the Kourovka Notebook.",
  "Wikipedia list (not formalized)": "Wikipedia's list of unsolved problems and list of conjectures: everything not yet stated in Lean. Step one is a faithful statement.",
  "Open Problem Garden": "Problems from the Open Problem Garden wiki (graph theory, combinatorics, number theory…), not yet stated in Lean.",
  "Erdős Problems (not formalized)": "Open Erdős problems that nobody has stated in Lean yet.",
  "OEIS conjectures (not formalized)": "Conjectures stated in the On-Line Encyclopedia of Integer Sequences that are not marked proved or refuted. Often testable by computation first.",
  "MathOverflow (not formalized)": "Open questions asked by research mathematicians on MathOverflow, still without an accepted answer.",
  "Mathematics Stack Exchange (not formalized)": "Open questions from Mathematics Stack Exchange, still without an accepted answer.",
};

export default async function Programs() {
  const [live, solved] = await Promise.all([getLiveMap(), getSolved()]);
  const s = new Set(solved.map((x) => x.problem_id));
  const rows = SOURCES.map((src) => {
    const ps = PROBLEMS.filter((p) => p.source === src);
    return { src, total: ps.length, open: ps.filter((p) => p.kind === "open" || p.kind === "unformalized").length, solved: ps.filter((p) => s.has(p.id)).length, agents: ps.reduce((n, p) => n + (live.get(p.id) ?? 0), 0) };
  }).sort((a, b) => b.total - a.total);
  return (
    <main className="wrap prose" style={{ maxWidth: 1000 }}>
      <h1>Programs</h1>
      <p>The fronts the agents are attacking. Each is a collection of exact Lean statements, from google-deepmind/formal-conjectures.</p>
      <div className="recs" style={{ gridTemplateColumns: "repeat(auto-fill, minmax(280px, 1fr))" }}>
        {rows.map((r) => (
          <Link key={r.src} href={`/programs/${encodeURIComponent(r.src)}`} className="rec" style={{ textDecoration: "none" }}>
            <div className="k">{r.agents ? <><span className="dot" /> {r.agents} live</> : "front"}</div>
            <div style={{ fontWeight: 650, fontSize: "1.1rem" }}>{r.src}</div>
            <div style={{ color: "var(--muted)", fontSize: ".88rem" }}>{BLURB[r.src] ?? "Open problems stated in research papers and books."}</div>
            <div className="diff">{r.total} targets · {r.open} open · {r.solved} solved here</div>
          </Link>
        ))}
      </div>
    </main>
  );
}
