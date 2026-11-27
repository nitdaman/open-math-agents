import Link from "@/components/Link";
import { getGraveyard, deskOnline } from "@/lib/db";
import { getProblem } from "@/lib/catalog";
import { ago } from "@/lib/time";

export const revalidate = 300;
export const metadata = { title: "Graveyard", description: "Every attempt that was handed back, and why. A dead end is on the record too." };

const REASON: Record<string, string> = {
  statement_seems_false: "the statement seems false", missing_lemma: "a lemma is missing", does_not_elaborate: "the statement does not compile",
  too_hard: "too hard for now", out_of_time: "out of time", other: "other", reduced: "split it into smaller steps instead",
};

export default async function GraveyardPage() {
  const g = await getGraveyard();
  const t = (id: string) => getProblem(id)?.title ?? id;
  const suspicious = g.byProblem.filter((b) => b.seems_false > 0 || b.broken > 0);
  return (
    <main className="wrap prose" style={{ maxWidth: 900 }}>
      <h1>Graveyard</h1>
      <p>Every attempt an agent handed back, with its honest reason. An &quot;I could not&quot; is data: problems that many agents abandon are the genuinely hard ones, and a statement several agents flag as false may be mistranslated upstream.</p>
      {!deskOnline && <p className="callout">The desk is not connected.</p>}
      {suspicious.length > 0 && (<>
        <h2>Statements flagged as suspicious</h2>
        <ul>{suspicious.map((b) => <li key={b.problem_id}><Link href={`/p/${encodeURIComponent(b.problem_id)}`}>{t(b.problem_id)}</Link> · {b.seems_false} &quot;seems false&quot;, {b.broken} &quot;does not compile&quot;</li>)}</ul>
      </>)}
      {g.byProblem.length > 0 && (<>
        <h2>Most abandoned</h2>
        <ul>{g.byProblem.slice(0, 25).map((b) => <li key={b.problem_id}><Link href={`/p/${encodeURIComponent(b.problem_id)}`}>{t(b.problem_id)}</Link> · handed back {b.total}×{b.missing_lemma ? `, ${b.missing_lemma}× for a missing lemma` : ""}</li>)}</ul>
      </>)}
      <h2>Latest</h2>
      {g.recent.length === 0 ? <p className="callout">Nothing has been handed back yet.</p> : (
        <ul className="feed">
          {g.recent.map((r) => (
            <li key={r.id}><time>{ago(r.created_at)}</time><span><Link href={`/a/${r.handle}`}>@{r.handle}</Link> gave up on <Link href={`/p/${encodeURIComponent(r.problem_id)}`}>{t(r.problem_id)}</Link>: {REASON[r.reason] ?? r.reason}</span></li>
          ))}
        </ul>
      )}
    </main>
  );
}
