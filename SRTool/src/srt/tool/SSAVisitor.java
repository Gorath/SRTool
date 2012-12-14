package srt.tool;

import java.util.HashMap;
import java.util.Map;

import srt.ast.AssignStmt;
import srt.ast.Decl;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.visitor.impl.DefaultVisitor;

public class SSAVisitor extends DefaultVisitor {

    // Stores the mapping between a variable name and its current ssa index
    private Map<String, Integer> ssaIndex = new HashMap<String, Integer>();

    public SSAVisitor() {
        super(true);
    }

    // Returns the variable name appended with the current ssa index
    // If the variable mapping does not exists it creates one
    private String getSSAName(String name) {
        if (ssaIndex.get(name) == null) ssaIndex.put(name,0);
        int i = ssaIndex.get(name);
        return name + "$" + i;
    }

    // Increments the ssa index for the corresponding variable
    private void incrementSSAIndex(String name) {
        int i = ssaIndex.get(name) + 1;
        ssaIndex.put(name, i);
    }

    // Creates a new declare statement with the corresponding ssa name
    @Override
    public Object visit(Decl decl) {
        String ssaName = getSSAName(decl.getName());
        return new Decl(ssaName, decl.getType(), decl);
    }

    // Replaces the name of the variable with its corresponding ssa name
    @Override
    public Object visit(DeclRef declRef) {
        String ssaName = getSSAName(declRef.getName());
        return super.visit(new DeclRef(ssaName, declRef));
    }

    // Visit the right hand side first so that it uses the previous ssa name
    // Increment the ssa index
    // Then replace the name of the variable with its corresponding ssa name
    @Override
    public Object visit(AssignStmt assignment) {
        Expr expr = (Expr) super.visit(assignment.getRhs());
        String name = assignment.getLhs().getName();
        incrementSSAIndex(name);
        DeclRef declRef = (DeclRef) visit(assignment.getLhs());
        return new AssignStmt(declRef, expr, assignment);
    }
}
