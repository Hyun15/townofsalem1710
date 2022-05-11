#lang forge

abstract sig Agent {}
sig Town extends Agent{}
sig Mafia extends Agent {}
sig Neutral extends Agent {}

sig Jester extends Neutral {}
sig SerialKiller extends Neutral {}
sig Executioner extends Neutral {}


abstract sig State {
    alive: set Agent,
    next: lone State
}

sig Day extends State {
    votes_for: pfunc Agent -> Agent,
    voted_out: lone Agent
}

sig Night extends State {
    mafia_killed: lone Agent,
    neutral_killed: set Agent
}

one sig endStats {
    winners: set Agent
}


-------------------------------------------------------------------------------
// Town Behavior

pred townPassive {
    all d: Day | {
        all t: Town | {
            no d.votes_for[t]
        }
    }
}

pred townMurderous {
    all d: Day | {
        all t: Town | {
            some d.votes_for[t]
            d.votes_for[t] != t
        }
    }
}

-------------------------------------------------------------------------------
// Mafia Behavior

pred mafiaWellFormed {
    -- mafia never vote other mafia
    all d: Day | {
        all m: Mafia | {
            not d.votes_for[m] in Mafia
        }
    }

    -- mafia never kill other mafia
    all n: Night | {
        all m: Mafia | {
            n.mafia_killed != m
        }
        // all a: Agent | {
        //     a = n.mafia_killed implies a in n.alive
        // }
    }
}

pred mafiaPassive {
    all n: Night | {
        no n.mafia_killed
    }
}

pred mafiaKilling {
    all n: Night | {
        some m: Mafia | m in n.alive
        some a: Agent | {
            a in n.alive
            a not in Mafia
        }
    } => {
        some n.mafia_killed
    }
}

-------------------------------------------------------------------------------

pred wellFormed {
    mafiaWellFormed

    -- all States should be either a Day or a Night
    State in (Day + Night)
    Agent in (Town + Mafia + Neutral)

    -- after each Day is a Night
    all d: Day | {
        some (d.next) => d.next in Night
    }

    -- after each Night is a Day
    all n: Night | {
        some (n.next) => n.next in Day
    }

    -- all Agents are alive in the first State
    all s: State | {
        no next.s implies s.alive = Agent
    }

    -- no one can come back to life
    all s: State | {
        all a: Agent | {
            a not in s.alive implies a not in s.next.alive
        }
    }

    -- ensuring normal voting behavior (alive can vote, vote for alive)
    all a: Agent | all d: Day | some d.votes_for[a] implies a in d.alive
    all a: Agent | all d: Day | some d.votes_for.a implies a in d.alive

    -- death occurs in the Night only if you are in mafia_killed or neutral_killed
    all n: Night | {
        all a: Agent | {
            a in n.alive
            (a = n.mafia_killed or a in n.neutral_killed)
        } => {
            a not in n.next.alive
        }
    }

    -- you cannot die in the Night unless you've been killed
    all n: Night | {
        all a: Agent | {
            a in n.alive
            a != n.mafia_killed
            a not in n.neutral_killed
            some n.next
        } => {
            a in n.next.alive
        }
    }

    -- death occurs in the Day only if you are voted out
    all d: Day | {
        all a: Agent | {
            some d.next
            a in d.alive
            (#{d.votes_for.a} > divide[#{d.alive}, 2])
        } => {
            a not in d.next.alive
            a in d.voted_out
        }
    }

    -- you cannot die in the Day unless you've been voted out
    all d: Day | {
        all a: Agent | {
            some d.next
            a in d.alive
            not (#{d.votes_for.a} > divide[#{d.alive}, 2])
        } => {
            a in d.next.alive
            a not in d.voted_out
        }
    }

}

run {
    wellFormed
    townPassive
    mafiaKilling

    some disj n1, n2, n3, n4: Night | {
        some disj a1, a2, a3, a4: Agent | {
            a1 in n1.mafia_killed
            a2 in n2.mafia_killed
            a3 in n3.mafia_killed
            a4 in n4.mafia_killed
        }
    }
} for exactly 9 State, exactly 2 Mafia, exactly 4 Town for (next is linear)
