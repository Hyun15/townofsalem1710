#lang forge

--------------------------------------------------------------------------------
// AGENTS

-- all players in the game are Agents
abstract sig Agent {}

-- there are three types of Agents: Town, Mafia, and Neutrals
sig Town extends Agent {}
sig Mafia extends Agent {}
sig Neutral extends Agent {} 


-- the Neutral Agents have special win conditions:
sig Jester extends Neutral {}
sig SerialKiller extends Neutral {}
sig Executioner extends Neutral {
    target: one Agent
}

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
    mafia_killed: set Agent,
    neutral_killed: set Agent
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
    all d: Day | all t: Town | one a: Agent | {
        a in d.alive
        a != t
        t in d.alive implies d.votes_for[t] = a
    }
}

// pred townHalfVotes {
//     -- during all Day states, half of the town votes for someone
// }

-------------------------------------------------------------------------------
// NEUTRAL BEHAVIOR

pred jesterBehavior {
    -- during the Day, vote yourself
    all d: Day | all j: Jester | {
        d.votes_for[j] = j
    }
}

--NOTE: there can only be one SerialKiller
pred serialKillerBehavior {
    -- during the Day, vote for anyone except yourself
    all d: Day | {
        some sk: SerialKiller, a: Agent | {
            d.votes_for[sk] = a
        }  
    }
    
    all n: Night | {
        some sk: SerialKiller | sk in n.alive

    } implies {
        #{n.neutral_killed} = 1
    }
}

pred executionerBehavior {
    -- guard to ensure the executioner's target is not themselves
    all e: Executioner | {
        e.target != e
    }
    -- during the Day, the Executioner votes for their target if the target is alive; if not, don't vote
    all d: Day | all e: Executioner | {
        e.target in d.alive implies d.votes_for[e] = e.target else d.votes_for[e] = none
    }

}
--------------------------------------------------------------------------------
// MAFIA BEHAVIOR

pred mafiaPabloEscobarBehavior{
    -- everynight, if someone in the mafia is alive, the mafia will kill someone
    all n: Night | {
        some m: Mafia | m in n.alive
        some t: Town | t in n.alive
    } => {
        #{n.mafia_killed} = 1
    }
    -- never vote for the mafia during the day
    all d: Day | {
        no m: Mafia | d.votes_for[m] in Mafia
    }
}

pred mafiaWeirdlyPeacefulBehavior{
--Do nothing during the night
all n: Night | {
    no (n.mafia_killed)
}
-- Never vote for other mafia during the day.
all d: Day | {
        no m: Mafia | d.votes_for[m] in Mafia
    }
}

--------------------------------------------------------------------------------
pred wellFormed {
    -- all states must be Day or Night
    State in (Day + Night)


    -- controls day behavior
    all d: Day | {
            -- no one can vote for themselves
            -- no a: Agent | d.votes_for[a] = a
            -- next is a night state
        some(d.next) => d.next in Night
    }

    -- controls night behavior
    all n: Night | {
        -- mafia cant kill mafia
        no m: Mafia | {
            m in n.mafia_killed
        }
        --next is a day state
        some(n.next) => n.next in Day
    }
-------------------------------------------------------------------------------
    -- creates an initial and final day
    some disj init, final: State {
        -- initial day properties
        no s: State | s.next = init
        all a: Agent | a in init.alive
    }

    -- ensuring normal voting behavior
    all a: Agent | all d: Day | some d.votes_for[a] implies a in d.alive
    all a: Agent | all d: Day | some d.votes_for.a implies a in d.alive

    all s: State | {
        some s.next implies s.next.alive in s.alive
    }

    all n: Night | {(n.mafia_killed + n.neutral_killed) in n.alive}
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

    all n: Night | {
        -- the net days alive it n alive minus mafia killed and whoever else
        some (n.next) => {
            n.next.alive = (n.alive - (n.mafia_killed + n.neutral_killed))
        }
    }

}


run {
    traces
    wellFormed 
    townMurderousBehavior
    mafiaWeirdlyPeacefulBehavior
    serialKillerBehavior
    // jesterBehavior
    // executionerBehavior

    } for exactly 3 State, exactly 2 Town, exactly 1 SerialKiller for {next is linear} 



------------------------------------------------------------------------------
// Property-Based Testing

// pred jester_wins {
//     some final: State | {

//     }
// }

// test expect {
//     vacuity: {
//         traces
//         wellFormed
//         }

//     // impossible_jester_win: {
//     //     traces
//     //     wellFormed
//     //     townPassiveBehavior
//     //     mafiaWeirdlyPeacefulBehavior
//     //     neutralBehavior
//     //     }




// }