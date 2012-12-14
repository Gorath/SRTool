package srt.ast;

import java.util.ArrayList;
import java.util.List;

public class DeclList extends Node {

	public DeclList(Decl[] decls) {
		this(decls, null);
	}
	
	public DeclList(Decl[] decls, Node basedOn) {
		super(basedOn);
		for(Decl decl : decls) {
			children.add(decl);
		}
	}
	
	@SuppressWarnings("unchecked")
	public List<Decl> getDecls() {
		return (List<Decl>)children.clone();
	}

//    @Override
//    public ArrayList<Node> getModSet() {
//        ArrayList<Node> result = new ArrayList<Node>();
//        for ( Decl d : getDecls()){
//            result.addAll(d.getModSet());
//        }
//        return result;
//    }
}
