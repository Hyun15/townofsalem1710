#lang forge

--------------------------------------------------------------------------------
// AGENTS

-- all players in the game are Agents
abstract sig Agent {}

-- there are three types of Agents: Town, Mafia, and Neutrals
sig Town extends Agent {}
sig Mafia extends Agent {}
// sig Neutral extends Agent {} 


-- the Neutral Agents have special win conditions:
// sig Jester extends Neutral {}
// sig SerialKiller extends Neutral {}
// sig Executioner extends Neutral {
//     target: one Agent
// }

/*
-the Jester wins by being killed during the Day cycle at any point
-the SerialKiller wins by being the only Agent alive at the end
-the Executioner wins if their target is killed while they're alive
*/

--------------------------------------------------------------------------------
// STATES

-- each State represents a day-night shift in the game
abstract sig State {
    alive: set Agent,
    // prev: lone State,
    next: lone State
    // stats: one endStat
}

-- each Day cycle, an Agent can vote for another Agent
-- the Agent that accrues >50% of votes is killed in the Day
sig Day extends State {
    votes_for: pfunc Agent -> Agent
}

-- each Night cycle, a set of Agents can be killed
sig Night extends State {
    mafia_killed: lone Agent
    // neutral_killed: set Agent
    // set Agent: protected
}

// sig endStats {
//     vote_killed: set Agent,
//     mafia_killed: set Agent,
//     neutral_killed: set Agent
// }
--------------------------------------------------------------------------------
// TOWN BEHAVIOR

pred townPassiveBehavior {
    -- during all Day states, the town should never vote
    all d: Day | all t: Town | {
        d.votes_for[t] = none
    }
}

pred townMurderousBehavior {
    -- during all Day states, the town should always vote for someone that's alive and not them
    // all d: Day | all t: Town | one a: Agent | {
    //     a in d.alive
    //     a != t
    //     t in d.alive implies d.votes_for[t] = a
    // }

    all d: Day | {
        all t: Town | t in d.alive implies {
            some d.votes_for[t]
            d.votes_for[t] != t
        }
    }
}

--------------------------------------------------------------------------------
// MAFIA BEHAVIOR

pred mafiaMurderousBehavior{
    // -- for every night...
    // all n: Night | {
    //     -- if there is some mafia alive
    //     some m: Mafia | m in n.alive
    //     -- and some town member alive
    //     some t: Town | t in n.alive
    // } => {
    //     -- the mafia will kill exactly one person
    //     #{n.mafia_killed} = 1
    // }

    // -- never vote for the mafia during the day
    // all d: Day | {
    //     no m: Mafia | d.votes_for[m] in Mafia
    // }

    all n: Night | {
        some m: Mafia | m in n.alive
        some t: Town | t in n.alive
    } => {
        some n.mafia_killed
    }

    all d: Day | {
        no m: Mafia | d.votes_for[m] in Mafia
    }
}

pred mafiaPeacefulBehavior{
    -- for all nights, the mafia_killed count equals 0
    all n: Night | {
        no n.mafia_killed
    }

    -- for all days, the mafia votes for someone not in the mafia
    all d: Day | {
        no m: Mafia | d.votes_for[m] in Mafia
    }

// --Do nothing during the night
// all n: Night | {
//     no (n.mafia_killed)
// }
// -- Never vote for other mafia during the day.
// all d: Day | {
//         no m: Mafia | d.votes_for[m] in Mafia
//     }
}

-------------------------------------------------------------------------------

pred wellFormed {
    -- all states must be Day or Night
    State in (Day + Night)

    -- all agents are Town and Mafia
    Agent in (Town + Mafia)

    -- controls day behavior
    all d: Day | {
        some (d.next) => d.next in Night
    }

    -- controls night behavior
    all n: Night | {
        -- mafia cant kill mafia
        some n.mafia_killed implies n.mafia_killed not in Mafia
        -- next is a day state
        some (n.next) => n.next in Day
    }

    -- there is some initial Night state
    some init: Night | {
        -- where there is no state previous
        no s: State | s.next = init
        -- and all Agents begin alive
        all a: Agent | a in init.alive
    }

    -- there is some final Day state
    some final: State | {
        -- where there is no next state
        no final.next
        all s: State | no s.next implies s = final
    }

    -- ensuring normal voting behavior (alive can vote, vote for alive)
    all a: Agent | all d: Day | some d.votes_for[a] implies a in d.alive
    all a: Agent | all d: Day | some d.votes_for.a implies a in d.alive

    -- no one can come back to life in the next state
    all s: State | {
        some s.next implies s.next.alive in s.alive
    }

    -- you can only kill that which is alive
    all n: Night | {(n.mafia_killed) in n.alive}    /// add neutral.killed
}


pred traces {
    all d: Day | {
        -- if someone gets a majority of the votes, then the next stats has that
        -- person gone
        all a: Agent | (#{d.votes_for.a} > divide[#{d.alive}, 2]) => {
            some d.next => {
                not a in d.next.alive
                // a in d.stats.vote_killed
            }
        } else {
            some d.next => a in d.next.alive
        }
    }

        -- the next days alive it n alive minus mafia killed and whoever else
        // some n.next => {
        //     n.next.alive = (n.alive - (n.mafia_killed)) // add neutralkilled
        // }
        // some n.next implies {
        //     all a: Agent | {
        //         (a in n.mafia_killed) implies (a not in n.next.alive)
        //         (a != n.mafia_killed and some n.next) implies a in n.next.alive
        //     }
        // }
    // }
    all n: Night | {
        some n.next implies {
            all a: Agent | {
                a in n.next.alive iff a != n.mafia_killed
            }
        }
    }
}

run {
    traces
    wellFormed
    townMurderousBehavior
    mafiaMurderousBehavior
    // some n: Night | {
    //     #{n.mafia_killed} = 0
    //     some n.next
    // }
} for exactly 3 Day, exactly 4 Night, exactly 3 Town, exactly 4 Mafia, 8 Int for {next is linear}