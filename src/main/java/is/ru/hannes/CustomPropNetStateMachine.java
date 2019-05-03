package is.ru.hannes;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlRelation;
import org.ggp.base.util.gdl.grammar.GdlSentence;
//import org.ggp.base.util.propnet.architecture.Component;
//import org.ggp.base.util.propnet.architecture.PropNet;
//import org.ggp.base.util.propnet.architecture.components.Proposition;
//import org.ggp.base.util.propnet.factory.OptimizingPropNetFactory;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.SimpleMachineState;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.query.ProverQueryBuilder;

import is.ru.cadia.ggp.propnet.structure.GGPBasePropNetStructureFactory;
import is.ru.cadia.ggp.propnet.structure.PropNetStructureFactory;
import is.ru.cadia.ggp.propnet.structure.PropNetStructure;
import is.ru.cadia.ggp.propnet.PropNetMove;
import is.ru.cadia.ggp.propnet.structure.components.BaseProposition;
import is.ru.cadia.ggp.propnet.structure.components.StaticComponent;
import is.ru.cadia.ggp.propnet.structure.components.StaticComponent.Type;

import java.io.File;
import java.util.List;

import org.ggp.base.util.game.Game;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.implementation.prover.ProverStateMachine;

import is.ru.cadia.ggp.utils.IOUtils;


@SuppressWarnings("unused")
public class CustomPropNetStateMachine extends StateMachine {
    /** The player roles */
    private List<Role> roles;
    PropNetStructure structure;
    /**
     * Initializes the PropNetStateMachine. You should compute the topological
     * ordering here. Additionally you may compute the initial state here, at
     * your discretion.
     */
    @Override
    public void initialize(List<Gdl> description) {
        //PropNetStructureFactory factory = new GGPBasePropNetStructureFactory();
        //PropNetStructure structure = factory.create(description);
        PropNetStructureFactory factory = new GGPBasePropNetStructureFactory();
        try {
            structure = factory.create(description);
        }
        catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    public Boolean reason(StaticComponent component, MachineState state, List<Move> moves) {
        // If we've already computed the value
        if (((CustomMachineState) state).observed(component.id)) {
            return ((CustomMachineState) state).bs.get(component.id);
        }

        // Base cases
        if (component.type == Type.TRUE) {
            return true;
        }
        else if (component.type == Type.FALSE) {
            return false;
        }
        else if (component.type == Type.PIPE) {
            int predId = component.inputs[0];
            Boolean predValue = reason(this.structure.getComponent(predId), state, null);
            ((CustomMachineState) state).bs.set(predId, predValue);
            return predValue;
        }
        else if (component.type == Type.NOT) {
            int predId = component.inputs[0];
            Boolean predValue = !reason(this.structure.getComponent(predId), state, null);
            ((CustomMachineState) state).bs.set(predId, predValue);
            return predValue;
        }
        else if (component.type == Type.INPUT) {
            for (Move m : moves) {
                if (((PropNetMove) m).getInputComponent().id == component.id) {
                    ((CustomMachineState) state).bs.set(component.id, true);
                    return true;
                }
            }
            return false;
        }
        else if (component.type == Type.INIT) {
            if (moves.size() == 0) {
                ((CustomMachineState) state).bs.set(component.id, true);
                return true;
            }
            return false;
        }


        // Below are cases where there are many input nodes, and not just 1

        Boolean pValue = false;

        // If we're doing an AND, we want it to be true by default, as otherwise it would always be false
        if (component.type == Type.AND) {
            pValue = true;
            for (int predId : component.inputs) {
                StaticComponent pred = this.structure.getComponent(predId);
                Boolean predValue = reason(pred, state, null);
                pValue &= predValue;
                ((CustomMachineState) state).set(predId, predValue);
            }
        }
        else if (component.type == Type.OR) {
            for (int predId : component.inputs) {
                StaticComponent pred = this.structure.getComponent(predId);
                Boolean predValue = reason(pred, state, null);
                pValue |= predValue;
                ((CustomMachineState) state).set(predId, predValue);
            }
        }
        return pValue;
    }

    /**
     * Computes if the state is terminal. Should return the value
     * of the terminal proposition for the state.
     */
    @Override
    public boolean isTerminal(MachineState state) {
        // TODO: Compute whether the MachineState is terminal.
        return reason(this.structure.getTerminalProposition(), state, null); 
    }

    /**
     * Computes the goal for a role in the current state.
     * Should return the value of the goal proposition that
     * is true for that role. If there is not exactly one goal
     * proposition true for that role, then you should throw a
     * GoalDefinitionException because the goal is ill-defined.
     */
    @Override
    public int getGoal(MachineState state, Role role)
            throws GoalDefinitionException {
        // TODO: Compute the goal for role in state.
        return -1;
    }

    /**
     * Returns the initial state. The initial state can be computed
     * by only setting the truth value of the INIT proposition to true,
     * and then computing the resulting state.
     */
    @Override
    public MachineState getInitialState() {
        // TODO: Compute the initial state.

        CustomMachineState state = new CustomMachineState(structure);
        for (BaseProposition bp : structure.getBasePropositions()) {
            state.set(bp.id, bp.initialValue);
        }
        
        return state;
    }

    /**
     * Computes the legal moves for role in state.
     */
    @Override
    public List<Move> getLegalMoves(MachineState state, Role role)
            throws MoveDefinitionException {
        // TODO: Compute legal moves.
        PropNetMove[] moves = this.structure.getPossibleMoves(this.structure.getRoleId(role));
        List<Move> legalMoves = new LinkedList<Move>();
        for (PropNetMove m : moves) {
            // I dont think the moves parameter is needed when calling reason here
            if (reason(m.getLegalComponent(), state, null)) {
                legalMoves.add((Move) m);
            }
        }
        return null;
    }

    /**
     * Computes the next state given state and the list of moves.
     */
    @Override
    public MachineState getNextState(MachineState state, List<Move> moves)
            throws TransitionDefinitionException {
        // TODO: Compute the next state.
        return null;
    }

    /* Already implemented for you */
    @Override
    public List<Role> getRoles() {
        return roles;
    }


    public static void main(String[] args) throws Exception {
        // setting up the state machine
        String gdlFileName = "/home/hannes/Documents/reasoner/games/games/ticTacToe/ticTacToe.kif";
        String gameDescription = IOUtils.readFile(new File(gdlFileName));
        String preprocessedRules = Game.preprocessRulesheet(gameDescription);
        Game ggpBaseGame = Game.createEphemeralGame(preprocessedRules);
        StateMachine stateMachine = new CustomPropNetStateMachine(); // insert your own machine here
        stateMachine.initialize(ggpBaseGame.getRules());

        List<Move> legalMoves = stateMachine.getLegalMoves(stateMachine.getInitialState(), );

        // some testing
        MachineState s0 = stateMachine.getInitialState();
    }

}