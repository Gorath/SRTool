package srt.tool;

import srt.ast.*;
import srt.ast.visitor.impl.DefaultVisitor;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

public class LoopAbstractionVisitor extends DefaultVisitor {

	public LoopAbstractionVisitor() {
		super(true);
	}

	@Override
	public Object visit(WhileStmt whileStmt) {

        List<Stmt> statements = new ArrayList<Stmt>();

        // Generates and store a list of statements for the assertions and assumptions
        List<Stmt> invariantAssertions =  new ArrayList<Stmt>();
        List<Stmt> invariantAssumptions =  new ArrayList<Stmt>();
        generateAssertionsAndAssumptions(invariantAssertions,invariantAssumptions,whileStmt);

        // Append invariant assertions first
        statements.addAll(invariantAssertions);


        // Find the list of variables that may be modified
        Stmt whileBody = whileStmt.getBody();
        ArrayList<Node> modset = whileBody.getModSet();
        ArrayList<DeclRef> filteredModset =  new ArrayList<DeclRef>();

        // Removes duplicate variables found in the modset
        for ( Node n : modset){
            boolean duplicate = false;
            for ( Node existing : filteredModset){
                 if (((DeclRef)existing).getName().equals(((DeclRef)n).getName()) ){
                     duplicate = true;
                     break;
                 }
            }
            if (!duplicate) filteredModset.add((DeclRef)n);
        }

        // Set each of the modified variables to be arbitrary
        // i.e. havoc all the variables in the modset
        List<Stmt> havocs = new ArrayList<Stmt>();
        for (DeclRef variable :filteredModset){
            havocs.add(new HavocStmt(variable));
        }
        statements.addAll(havocs);

        // Append invariant assumptions that were generated before
        statements.addAll(invariantAssumptions);

        // Execute loop body once inside an if statement
        List<Stmt> ifBody = new ArrayList<Stmt>();

        removeBlockStatements(ifBody,whileBody);

        // Append invariant assertions to ensure all the invariants hold before
        // executing the loop body
        ifBody.addAll(invariantAssertions);

        // Assume falsity to prevent any further executions
        ifBody.add(new AssumeStmt(new IntLiteral(0)));

        // Append if statement
        Stmt ifStmt = new IfStmt(whileStmt.getCondition(),new BlockStmt(ifBody),new EmptyStmt(), whileStmt);
        statements.add(ifStmt);

        return super.visit(new BlockStmt(statements,whileStmt));
	}

    private void removeBlockStatements(List<Stmt> ifBody, Stmt whileBody) {
        if ( whileBody instanceof BlockStmt){
            ifBody.addAll(((BlockStmt)whileBody).getStmtList().getStatements());
        }   else{
            ifBody.add(whileBody);
        }
    }

    private void generateAssertionsAndAssumptions(List<Stmt> assertions, List<Stmt> assumptions , WhileStmt whileStmt){
        ExprList invariantsList = whileStmt.getInvariantList();
        for ( Expr e : invariantsList.getExprs()){
               assertions.add(new AssertStmt( e ,e ));
               assumptions.add(new AssumeStmt(e, e));
        }
    }

}
