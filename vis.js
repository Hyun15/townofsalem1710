const d3 = require('d3')
d3.selectAll("svg > *").remove();



let listOfStates = State.atoms(true);
let hi = next.tuples()

const notInit = [];
let init;
for(const state of listOfStates){
    if(state.next.toString()){
        notInit.push(state.next)
    }
   }
for(const state of listOfStates){
    if(!notInit.includes(state)){
        init = state
    }
}
console.log(init.id())

let statesInOrder = [init]
let lastAdded = init
while(lastAdded.next.toString()){
    statesInOrder.push(lastAdded.next)
    lastAdded = lastAdded.next;
}
listOfStates = statesInOrder



const stateHeight = height / listOfStates.length;

const theSvg = d3.select(svg);

function showState(number, state){
const topOfState = number*stateHeight
const agentToLocationMap = {}
const living = state.alive.tuples()


let backgroundColor;

if(state.in(Day)){backgroundColor = '#64aded'}
if(state.in(Night)){backgroundColor = '#5f068c'}
    theSvg
    .append('rect')
    .attr('x', 0)
    .attr('y', topOfState)
    .attr('width', width)
    .attr('height', stateHeight)
    .style('fill', backgroundColor)

function cx(d,i){
const boxSize = width / living.length
const x = (i * boxSize) + (boxSize/2)
agentToLocationMap[d] = {x: x, y: topOfState + (stateHeight/2)}
return x
}

function colorFunc(d,i){
    if(d.in(Mafia)){
        return "#b50514"
    }
    if(d.in(Town)){
        return "#14b505"
    }
    if(d.in(Jester)){
        return "#de14c3"
    }
    if(d.in(SerialKiller)){
        return "#1436de"
    }
    if(d.in(Executioner)){
        return "#5e616e"
    }
}

theSvg.selectAll("agents")
      .data(living)
      .join("circle")
      .attr("cy", topOfState + (stateHeight/2))
      .attr("cx", cx)
      .attr("r", stateHeight/10)
      .style("fill", colorFunc)



if(state.in(Day)){
    // We want to put the name of the person each peron voted for right under 
}
if(state.in(Night)){
    
}
}




for (const [index, element] of listOfStates.entries()) {
    showState(index, element);
  }

