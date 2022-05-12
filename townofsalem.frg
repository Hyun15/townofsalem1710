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
    mafia_killed: lone Agent,
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
    -- for every night...
    all n: Night | {
        -- if there is some mafia alive
        some m: Mafia | m in n.alive
        -- and some town member alive
        some t: Town | t in n.alive
    } => {
        -- the mafia will kill exactly one person
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

-------------------------------------------------------------------------------
pred mafiaWellFormed {
    -- ensure that the mafia can never kill more than one person per night
    all n: Night | {
        #{n.mafia_killed} <= 1
    }

}

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

    // mafiaWellFormed
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
    // mafiaPabloEscobarBehavior
    // serialKillerBehavior
    // jesterBehavior
    // executionerBehavior
    some n: Night | {
        #{n.mafia_killed} = 1
        some n.next
        some n.next.next
    }

    } for exactly 8 State, exactly 4 Town, exactly 4 Mafia, 9 Int for {next is linear} 



-- what we know:
// states don't work after 3 for mafia/neutral (killing)
// the next night after a killing doesn't load


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