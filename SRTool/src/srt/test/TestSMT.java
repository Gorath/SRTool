package srt.test;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.util.Scanner;

import srt.exec.SMTQuery;

public class TestSMT {
	
	public static void main(String[] args) throws IOException, InterruptedException {
        Scanner sc = new Scanner(new File("queryIn.txt"));
        while(sc.hasNext()) System.out.println(sc.nextLine());
        SMTQuery query = new SMTQuery(new File("queryIn.txt"), 30000);
		String result = query.go();
		System.out.println("result");
        System.out.println(result);
	}
}
