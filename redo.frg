#lang forge

abstract sig Agent {}
sig Town extends Agent{}
sig Mafia extends Agent {}
sig Neutral extends Agent {}

sig Jester extends Neutral {}
lone sig SerialKiller extends Neutral {}
sig Executioner extends Neutral {
    target: one Agent
}


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
    all e: Executioner| e.target != e
    all n: Night |{
        some SerialKiller
        SerialKiller in n.alive
        #{n.alive} > 1
    } => #{n.neutral_killed} = 1 else{
        #{n.neutral_killed} = 0
    } 

    all n: Night | some SerialKiller => not SerialKiller in n.neutral_killed

    all n: Night | {
         some n.neutral_killed => n.neutral_killed in n.alive
    }
     
    all n: Night | {
        all sk: SerialKiller | sk not in n.alive implies #{n.neutral_killed} = 0
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

pred exeBehavior{
    all d: Day|{
        all e: Executioner |{
            (e in d.alive and e.target in d.alive) => d.votes_for[e] = e.target
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

pred jesterWins[j: Jester]{
    some d: Day | {
        some d.next
        j in d.alive
        not j in d.next.alive
        not townWins[d]
    }
}

pred exeWins[e: Executioner]{
    some d: Day | {
        some d.next
        d.voted_out = e.target
        e in d.alive
        not someoneWinsState[d]
    }
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
    some s: State | {
        no next.s
        all a: Agent | {
            a in s.alive
        }
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

    all d: Day | some d.voted_out => d.voted_out in d.alive

    -- someone will always win
    some s: State | {
        no s.next 
        someoneWinsState[s]
    }

}




// run {
//     wellFormed
//     some s: State | not townWins[s]
//     townPassive
//     mafiaPassive
// } for exactly 5 Agent, exactly 5 Town for {next is linear}



/*
run {
    wellFormed
    townMurderous
    mafiaKilling
    jesterBehavior
    serialKillerBehavior
    exeBehavior
    some j: Jester | jesterWins[j]
    some e: Executioner | exeWins[e]
    
} for 15 Agent,5 Int, 15 State, exactly 2 Mafia, exactly 1 Jester,exactly 1 SerialKiller, exactly 1 Executioner,exactly 5 Town for (next is linear)
*/

---------------------––––––––––––––––––---––-––--––––––––––––––––––––––
// Property-Based Testing

test expect {
    vacuity: {
        wellFormed
    } is sat

    townCanWin : {
        wellFormed
        some s: State | {
            townWins[s]
        } 
    } is sat

    mafiaCanWin : {
        wellFormed
        some s: State | {
            mafiaWins[s]
        }
    } is sat

    skCanWin : {
        wellFormed
        some s: State | {
            skWins[s]
        }
    } is sat

    jesterCanWin : {
        wellFormed
        some j : Jester | {
            jesterWins[j]
        }
    } is sat

    townPassiveWin: {
        wellFormed
        townPassive
        some s: State | {
            no s.next
            townWins[s]
        }
    } for exactly 5 Town, exactly 0 Mafia, exactly 0 Neutral is sat

    townAggressiveWin: {
        wellFormed
        townMurderous
        some s: State | {
            no s.next
            townWins[s]
        }
    } for exactly 5 Town, exactly 0 Mafia, exactly 0 Neutral is sat

    townPassiveLoss: {
        wellFormed
        townPassive
        mafiaKilling

        some s: State | {
            no s.next
            townWins[s]
        }

    } for exactly 5 Town, exactly 3 Mafia, exactly 0 Neutral is unsat

    townAggressiveLoss: {
        wellFormed
        townMurderous
        mafiaKilling
        some s: State | {
            no s.next
            townWins[s]
        }
    } for exactly 5 Town, exactly 3 Mafia, exactly 0 Neutral is unsat

    skWinsWhenAllPassive : {
        wellFormed
        townPassive
        mafiaPassive
        serialKillerBehavior
        no s: State | {
            skWins[s]
        }
    } for 15 State, exactly 5 Town, exactly 3 Mafia, exactly 1 SerialKiller, exactly 1 Neutral is unsat

    mafiaAlwaysAliveWin : {
        wellFormed
        serialKillerBehavior
        all s: State | {
            some m: Mafia | m in s.alive
        } 
        no s: State | {
            mafiaWins[s]
        }
        
    } for 15 State, exactly 5 Town, exactly 3 Mafia,exactly 0 Neutral is unsat

    
    mafiaVsTownTownWin : {
        wellFormed
        mafiaKilling
        townMurderous
        some Town
        some Mafia
        some s: State | townWins[s]
    } is sat

    // mafiaVsTownMafWin : {
    //     wellFormed
    //     mafiaKilling
    //     townMurderous
    //     some Town
    //     some Mafia
    //     some s: State | mafiaWins[s]
    // } for 25 State, 12 Day,13 Night ,exactly 8 Town, exactly 3 Mafia,exactly 0 Neutral, 6 Int is sat

    // skCantDieIfWins : {
    //     wellFormed
    //     serialKillerBehavior
    //     some s: State | {
    //         skWins[s]
    //     }
    //     some d: Day | {
    //         not SerialKiller in d.alive
    //     }
    // } for 12 State, exactly 3 Town, exactly 3 Mafia, exactly 1 SerialKiller, exactly 1 Neutral is unsat

    

}
