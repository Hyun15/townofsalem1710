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

pred townWinFlag[d: Day] {
    -- for the town to win...
}

-------------------------------------------------------------------------------
// NEUTRAL BEHAVIOR

pred jesterBehavior {
    -- during the Day, vote yourself
    all d: Day | all j: Jester | {
        d.votes_for[j] = j
    }
}

pred serialKillerBehavior {
    -- during the Day, vote for anyone except yourself
    all d: Day | all sk: SerialKiller | some a: Agent | {
        a in d.alive
        a != sk
        sk in d.alive implies d.votes_for[sk] = a
    }

    -- during the Night, the SerialKiller will kill any one random Agent that's not themselves
    all n: Night | all sk: SerialKiller | one a: Agent | {
        a in n.alive
        a != sk
        sk in n.alive implies a in n.neutral_killed
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

        // all s: State | no s.next implies s = final
        // all s: State | no next.s implies s = init


    }

    -- ensuring normal voting behavior
    all a: Agent | all d: Day | some d.votes_for[a] implies a in d.alive
    all a: Agent | all d: Day | some d.votes_for.a implies a in d.alive


    all s: State | no s.neutral_killed


}

    //

// pred wellFormed {
//     some disj firstDay, lastDay: Day | {
//         -- no state should come before the firstDay
//         no s: State | s.next = firstDay
//         // firstDay.prev = none
//         -- no state should exist after the lastDay
//         no lastDay.next
//         // all s: State | {s.prev != lastDay}

//         -- everyone is alive in the firstDay
//         all a: Agent | {
//             a in firstDay.alive
//         }

//         -- all other states should have one unique next
//         all s: State | {
//             (s != firstDay and s !=lastDay) implies some s.next
//         }
//         all disj s1, s2: State | {
//             s1.next != s2.next
//             s1.next = s2 implies s2.prev = s1
//         }

//         -- if someone dies in the night, they are not alive in the next Day
//         all n: Night | all a: Agent | {
//             a in n.mafia_killed implies a not in n.next.alive
//             a in n.neutral_killed implies a not in n.next.alive
//         }

//         -- everyone alive in the day is alive in the next night
//         ------ NOTE: this needs to change when voting becomes functional
//         all d: Day | all n: Night | {
//             d.next = n implies d.alive = n.alive
//         }

//     }



pred traces {
        
    all d: Day | {
        -- if someone gets a majority of the votes, then the next stats has that
        -- person gone
        all a: Agent | (#{d.votes_for.a} > divide[#{d.alive}, 2]) => {
            some d.next => d.next.alive = d.alive - a
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
    townPassiveBehavior
    mafiaWeirdlyPeacefulBehavior
    jesterBehavior
    serialKillerBehavior

    } for exactly 3 State, exactly 2 Town, exactly 2 Mafia for {next is linear}