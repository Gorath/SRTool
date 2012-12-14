package srt.tool;

import java.util.HashMap;
import java.util.Map;

import srt.ast.AssignStmt;
import srt.ast.Decl;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.visitor.impl.DefaultVisitor;

public class SSAVisitor extends DefaultVisitor {
    //stores the mapping between a variable name and its current ssa index
    private Map<String, Integer> index = new HashMap<String, Integer>();

    public SSAVisitor() {
        super(true);
    }

    // returns the variable name appended with the current ssa index
    // if the variable mapping does not exists it creates one
    private String getSSAName(String name) {
        if (index.get(name) == null) index.put(name,0);
        int i = index.get(name);
        return name + "$" + i;
    }

    //increments the index for the variable
    private void incrementSSAIndex(String name) {
        int i = index.get(name) + 1;
        index.put(name, i);
    }

    //this creates a new declares statement with the appropriate ssa name.
    @Override
    public Object visit(Decl decl) {
        String ssaName = getSSAName(decl.getName());
        return new Decl(ssaName, decl.getType(), decl);
    }

    //replaces the name of the variable with its current ssa name
    @Override
    public Object visit(DeclRef declRef) {
        String ssaName = getSSAName(declRef.getName());
        return super.visit(new DeclRef(ssaName, declRef));
    }


    //visit the right hand side. Increment the ssa index. and use the new index on the lhs
    @Override
    public Object visit(AssignStmt assignment) {
        Expr expr = (Expr) super.visit(assignment.getRhs());
        String name = assignment.getLhs().getName();
        incrementSSAIndex(name);
        DeclRef declRef = (DeclRef) visit(assignment.getLhs());
        return new AssignStmt(declRef, expr, assignment);
    }
}
