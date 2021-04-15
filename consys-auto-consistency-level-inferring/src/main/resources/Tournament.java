/*

@Inv(”forall(Player:p, Tournament:t) :− enrolled(p,t) =>
player(p) and tournament(t)”)
@Inv(”forall(Player:p,q, Tournament:t) :− inMatch(p,q,t) =>
enrolled(p,t) and enrolled(q,t) and (active(t) or finished(t))”)
@Inv(”forall(Player:p,Tournament:t) :− #enrolled(∗,t) <=
Capacity”)
@Inv(”forall(Tournament:t) :− active(t) => tournament(t)”)
@Inv(”forall(Tournament:t) :− finished(t) => tournament(t)”)
@Inv(”forall(Tournament:t) :− not( active(t) and finished(t))”)


public interface TournamentApp {
@True(”player (p)”)
RESULT add_player(Player p);

@True( ” t o u r n a m e n t ( t ) ” )
RESULT add_tourn(Tournament t);

@False( ” t o u r n a m e n t ( t ) ” )
RESULT rem_tourn(Tournament t);

@True(”enrolled (p, t )”)
RESULT enroll(Player p, Tournament t);

@False(”enrolled (p, t )”)
RESULT disenroll(Player p, Tournament t);

@True(” active(t) ”)
RESULT begin_tourn(Tournament t);

@True(” finished(t) ”)
@False(” active(t) ”)
RESULT finish_tourn(Tournament t);

@True(”inMatch(p, q, t )”)
RESULT do_match(Player p, Player q, Tournament t);
}
*/