package srt.tool;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import srt.ast.Expr;

public class SMTLIBConverter {

    private ExprToSmtlibVisitor exprConverter;
    private StringBuilder query;

    public SMTLIBConverter(Set<String> variableNames, List<Expr> transitionExprs, List<Expr> propertyExprs) {

        if(propertyExprs.size() == 0)
        {
            throw new IllegalArgumentException("No assertions.");
        }
        // create a StringBuilder with a decent amount of memory
        query = new StringBuilder(1600);

        // Start building the query string
        query.append( "(set-logic QF_BV)\n");
        query.append( "(declare-fun main() Bool)\n");

        // Function to convert a boolean to a bitvector of length 32 of either all 1's or all 0's
        query.append("(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");

        // Function to take a bit vector of length 32 and returns a bool
        // @result false if the input is all zeros
        // @result true otherwise
        query.append("(define-fun tobool ((p (_ BitVec 32))) (Bool) (not (= p (_ bv0 32))))\n");

        // Convert variable names to SMT-LIB syntax
        generateVariableNames(variableNames);

        //generate names for all the properties that will be used in the end.
        generateVariablesForProperties(propertyExprs);

        exprConverter = new ExprToSmtlibVisitor();

        // Convert transition expressions to SMT-LIB syntax
        generateTransitionExpressions(transitionExprs);

        //recursively generate all the  properties to represent assertions.
        query.append(generatePropertyPredicates(propertyExprs,0));

        //generate the final assertion
        query.append("(assert (not ");
        query.append(generatePropertyFormula(propertyExprs,0));
        query.append( ") )");

        //execute the query
        query.append("(check-sat)\n");

        //get the values for the properties as the result
        query.append("(get-value (");
        for (int i = 0; i < propertyExprs.size(); i++) {
            query.append("prop" + i + " ");
        }
        query.append("))");

        //very help full for debugging purposes.
        System.out.println(query.toString());
    }

    private void generateVariablesForProperties(List<Expr> propertyExprs) {
        for (int i = 0; i < propertyExprs.size(); i++) {
            query.append("(declare-fun prop" + i + " () (Bool))\n");
        }
    }

    private String generatePropertyPredicates(List<Expr> propertyExprs, int index) {
            if (index == propertyExprs.size()) return "";
            return "(assert (= prop" + index + " (tobool " + exprConverter.visit(propertyExprs.get(index)) + ")))\n" + generatePropertyPredicates(propertyExprs, index+1);
    }

    private void generateVariableNames(Set<String> variableNames ) {
        for (String currentVariable : variableNames) {
            query.append( "(declare-fun " + currentVariable + " () (_ BitVec 32))\n");
        }
    }

    private void generateTransitionExpressions(List<Expr> transitionExprs) {
        for (Expr exp : transitionExprs) {
            query.append( "(assert (tobool " + exprConverter.visit(exp) + "))\n");
        }
    }

    private String generatePropertyFormula(List<Expr> propertyExprs, int index) {
         if (index == propertyExprs.size() - 1) {
            return  "prop" + index;
         }
         return "(and prop" + index +  " " + generatePropertyFormula(propertyExprs, index+1) + ")";
    }

    public String getQuery() {
        return query.toString();
    }


}
