package is.ru.hannes;

import java.util.HashSet;
import java.util.Set;
import java.util.BitSet;
import java.util.Map;
import java.util.HashMap;

import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import is.ru.cadia.ggp.propnet.structure.PropNetStructure;
import is.ru.cadia.ggp.propnet.structure.components.BaseProposition;

public class CustomMachineState extends MachineState {

    public final BitSet bs;
    public final BitSet observedBs;
    public PropNetStructure structure;

    public CustomMachineState(PropNetStructure structure) {
        super();
        this.bs = new BitSet();
        this.observedBs = new BitSet();
        this.structure = structure;
    }

    public CustomMachineState(PropNetStructure structure, BitSet bs, BitSet observedBs) {
        super();
        this.structure = structure;
        this.bs = bs;
        this.observedBs = observedBs;
    }

    public void set(int key, Boolean value) {
        this.bs.set(key, value);
        this.observedBs.set(key);
    }

    public Boolean get(int key) {
        return this.bs.get(key);
    }

    public Boolean observed(int key) {
        return this.observedBs.get(key);
    }

    @Override
	public Set<GdlSentence> getContents() {
        // todo: need to convert bitset to Set<GdlSentence>

        Set<GdlSentence> ret = new HashSet<GdlSentence>();

        for (BaseProposition bp : this.structure.getBasePropositions()) {
            if (this.bs.get(bp.id)) {
                for (GdlSentence sentenceInBp : bp.sentences) {
                    ret.add(sentenceInBp);
                }
            }
        }

        return ret;
    }

    // Very likely that this isnt working
    @Override
    public CustomMachineState clone() {
        return new CustomMachineState(this.structure, this.bs, this.observedBs);
    }
}
