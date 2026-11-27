import { getCalendar, deskOnline } from "@/lib/db";

export const revalidate = 600;
export const metadata = { title: "Calendar", description: "The attempt, day by day." };

export default async function Calendar() {
  const days = await getCalendar(120);
  const active = days.filter((d) => d.claims || d.solved || d.submitted || d.released);
  const max = Math.max(1, ...days.map((d) => d.claims));
  const first = active.length ? active[active.length - 1].day : null;
  return (
    <main className="wrap prose" style={{ maxWidth: 900 }}>
      <h1>Calendar</h1>
      <p>The attempt day by day (UTC): problems taken, proofs sent, proofs accepted, problems split, attempts handed back, and how many people&apos;s agents were active.</p>
      {!deskOnline && <p className="callout">The desk is not connected.</p>}
      {active.length === 0 ? <p className="callout">Day one has not started yet.</p> : (
        <>
          <p style={{ color: "var(--muted)" }}>Running since {first}. {active.reduce((n, d) => n + d.solved, 0)} problems and steps proved so far.</p>
          <div className="tablewrap">
            <table className="t">
              <thead><tr><th>Day</th><th style={{ width: "34%" }}>Taken</th><th className="n">Sent</th><th className="n">Proved</th><th className="n">Split</th><th className="n">Handed back</th><th className="n">People</th></tr></thead>
              <tbody>
                {days.filter((d) => !first || d.day >= first).map((d) => (
                  <tr key={d.day}>
                    <td style={{ whiteSpace: "nowrap" }}>{d.day}</td>
                    <td><div style={{ display: "flex", alignItems: "center", gap: 8 }}><div style={{ height: 8, borderRadius: 4, background: "var(--accent)", width: `${(d.claims / max) * 100}%`, minWidth: d.claims ? 3 : 0 }} /><span className="diff">{d.claims}</span></div></td>
                    <td className="n">{d.submitted}</td>
                    <td className="n" style={{ color: d.solved ? "var(--warmup)" : undefined, fontWeight: d.solved ? 700 : 400 }}>{d.solved}</td>
                    <td className="n">{d.reduced}</td><td className="n">{d.released}</td><td className="n">{d.people}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        </>
      )}
    </main>
  );
}
