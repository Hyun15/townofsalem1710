#lang forge

abstract sig Agent {}
sig Town extends Agent{}
sig Mafia extends Agent {}
sig Neutral extends Agent {}

sig Jester extends Neutral {}
lone sig SerialKiller extends Neutral {}
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
            some d.votes_for[m] => not d.votes_for[m] in Mafia 
        }
    }
    all n: Night | {
        some n.mafia_killed implies n.mafia_killed in n.alive
        {no m: Mafia | m in n.alive} => no n.mafia_killed
    }

    -- mafia never kill other mafia
    all n: Night | {
        all m: Mafia | {
            n.mafia_killed != m
        }
         all a: Agent | {
             a = n.mafia_killed implies a in n.alive
         }
        all sk: SerialKiller | {
            n.mafia_killed != sk
        }
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
// NEUTRAL BEHAVIOR

pred neutralWellFormed{
    all n: Night |{
        some SerialKiller
        SerialKiller in n.alive
        #{n.alive} > 1
    } => #{n.neutral_killed} = 1 else{
        no n.neutral_killed
    } 

     all n: Night | some SerialKiller => not SerialKiller in n.neutral_killed

     all n: Night | {
         some n.neutral_killed => n.neutral_killed in n.alive
     }
}

pred jesterBehavior {
    -- during the Day, vote yourself
    all d: Day | all j: Jester | {
        j in d.alive => d.votes_for[j] = j
    }
}
pred serialKillerBehavior {
    -- during the Day, vote for anyone except yourself
    all d: Day | {
       all sk: SerialKiller | #{d.alive} > 1 => {
           sk in d.alive => some d.votes_for[sk]
           not d.votes_for[sk] = sk
       }
    }

}
--------------------------------------------------------------------------------
// WINNING CONDITIONS

pred townWins[s: State]{
    -- some town member is alive, mafia sk dead
    some t: Town | t in s.alive
    all m: Mafia | not m in s.alive
    all sk: SerialKiller | not sk in s.alive
}

pred mafiaWins[s: State]{
    some m: Mafia | m in s.alive
    all t: Town | not t in s.alive
    all sk: SerialKiller | not sk in s.alive
}

pred skWins[s: State]{
    all a: Agent | a in s.alive => a in SerialKiller
    some sk: SerialKiller | sk in s.alive
}

pred someoneWinsState[s: State]{
    skWins[s] or mafiaWins[s] or townWins[s]
}



-------------------------------------------------------------------------------

pred wellFormed {
    neutralWellFormed
    mafiaWellFormed

    -- all States should be either a Day or a Night
    State in (Day + Night)
    Agent in (Town + Mafia + Neutral)
    Neutral in (Jester + SerialKiller + Executioner)

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

    -- someone will always win
    some s: State | {
        no s.next 
        townWins[s]
    }

}

run {
    wellFormed
    townPassive
    mafiaKilling
    jesterBehavior
    serialKillerBehavior
    
} for 10 Agent,5 Int, 15 State, exactly 2 Mafia, exactly 1 Jester,exactly 1 SerialKiller, exactly 1 Executioner,exactly 4 Town for (next is linear)
