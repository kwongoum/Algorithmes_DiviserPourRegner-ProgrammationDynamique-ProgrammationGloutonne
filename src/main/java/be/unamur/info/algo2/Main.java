package be.unamur.info.algo2;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import com.google.common.base.Strings;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import java.lang.reflect.Array;
import java.util.stream.Stream;
import java.util.*;
import java.lang.*;


import java.util.stream.Stream;

public class Main {
    private static Logger myLog = LoggerFactory.getLogger(Main.class);
    //private static final String SPACE = " ";
    static int t = 0; // problem3: nombre de tests
    static String[] fileLines = new String[0];
    static  ArrayList<Integer> N = new ArrayList<>();
    static  ArrayList<List<Integer>> d = new ArrayList<>();

    /* ******* PROBLEM 1 NAIVE VERSION********************************************* */
        /*
        // pre-condtion
         @requires s_file !=null;
         @ requires \typeof(dataFile[0])== \type(Integer)
         @ requires ((Integer.parseInt(dataFile[0]) * 2) + 1 == dataFile.length);
         // post-condition
         @ensures  actionnairesTabLine.length != Integer.parseInt(dataFile [i - 1]) ==>
         @          \solution[j] = null;
         @ ensures  actionnairesTabLine.length == Integer.parseInt( dataFile [i - 1]) ==>
         @                  solution[j] = getActionnaireMajoritire(actionnairesTabLine);
         @ ensures dataFile.length >=3 ==> \result == solution;

         // invariant
         @invariant  i,j >=0;
         @loop_invariant(\forall int i, j; (i>=2)&& (i <dataFile.length) && (j>=0) &&
         @ j<= dataFile[i].length();
         @ invariant  actionnairesTabLine.length == Integer.parseInt( dataFile [i - 1]);
         //variant
         @increasing i+2;
         @increasing j+1;
         @*/




    public static String[] problem_1_naive(final String s_file) {
        // System.out.println("===");
        //System.out.println(s_file);
        //System.out.println("===");
        //String[] s_tmp = {"Goku", "Piccolo", null, "Gohan"};


        if (s_file == null) return null;
        myLog.info(" Let Start !!!...\n" + s_file);
        String[] dataFile = null;
        int numberOfTests;

        try {
            dataFile = s_file.split("\n");// chaque ligne du fichier va dans 1 case du tab
        } catch (Exception e) {
            System.err.println("Error opening file !!!");
        }

        try {
            numberOfTests = Integer.parseInt(dataFile[0]);
        } catch (NullPointerException e) {
            return null;
        }

        if (numberOfTests * 2 + 1 != dataFile.length) return null;

        String[] solution = new String[numberOfTests];

        for (int i = 2, j = 0; i < dataFile.length; i = i + 2, j++) { // j est l 'act majoritaire de la ligne i
            String[] actionnairesTabLine = dataFile[i].split(" ");
            if (actionnairesTabLine.length != Integer.parseInt(dataFile[i - 1]))

                return null;
            solution[j] = getActionnaireMajoritire(actionnairesTabLine);

        }
        return solution;
        // String[] s_tmp = null;
        // return s_tmp;
    }
    /* **************************** FONCTION UTILISEE DANNS PROBLEM_1 NAIVE ********************* */


    private static String getActionnaireMajoritire(String[] actionnairesTabLine) {

        Stream<String> myStream = Stream.of(actionnairesTabLine); //  transforme  en stream
        Map.Entry<String, Integer> resultIterator = myStream.collect
                (HashMap<String, Integer>::new,
                        (myMap, actionnaire) -> myMap.merge(actionnaire, 1, Integer::sum),
                        (map1, map2) -> {
                        }) // juste pour respecter la syntaxe
                .entrySet().stream().max(Map.Entry.comparingByValue()).get();

        if (resultIterator.getValue() > (actionnairesTabLine.length / 2))
            return resultIterator.getKey();
        else
            return null;
    }
    /* ******* PROBLEM 1 "DIVISER POUR REGNER " ********************************************* */

    public static String[] problem_1(String s_file) {
     /*   System.out.println("===");
          System.out.println(s_file);
          System.out.println("===");
         String[] s_tmp = {"Goku", "Piccolo", null, "Gohan"};
       */
        String[] s_tmp = null;
        if (s_file == null) return null;
        myLog.info(" Let Start !!!...\n" + s_file);
        String[] dataFile = null;
        int numberOfTests;

        try {
            dataFile = s_file.split("\n");// chaque ligne du fichier va dans 1 case du tab
        } catch (Exception e) {
            System.err.println("Error opening file !!!");
        }

        try {
            numberOfTests = Integer.parseInt(dataFile[0]);
        } catch (NullPointerException e) {
            return null;
        }

        if (numberOfTests * 2 + 1 != dataFile.length) return null;

        String[] responseForAllLine = new String[numberOfTests];

        for (int i = 2; i < dataFile.length; i = i + 2) {
            int numberOfActionnaires = Integer.parseInt(dataFile[i - 1]);
            String[] lineOfActionnaires = dataFile[i].split(" ");
            Map<String, Integer> map = new HashMap<>();


            if (numberOfActionnaires != lineOfActionnaires.length) return null;

            responseForAllLine[(i - 2) / 2] = getActionnaireMajoritaireDeLaLigne(lineOfActionnaires, 0,
                    numberOfActionnaires - 1, map);
        }
        return responseForAllLine;
        //return s_tmp;
    }

    /* *********** FUNCTION A UTILISER DANS PROBLEM 1 *DIVISER POUR REGNER ******************* */


     /*
       // pre-condtions
      @ requires map!=null;
      @ requires lineOfActionnaires!= null;
      @ requires low >= 0;
      @ requires low <= Integer.MAX_VALUE;
      @ requires high >= 0;
      @ requires high <= Integer.MAX_VALUE;
      @ requires (high ==low) ; // cas de base
      @ requires majoritaireSubArray1 ==  getActionnaireMajoritaireDeLaLigne(lineOfActionnaires, low,
      @                                                                     low + ((high - low) / 2), map)
      @  && majoritaireSubArray2 == getActionnaireMajoritaireDeLaLigne(lineOfActionnaires,
      @                                                             (low + ((high -low ) / 2) + 1), high, map);
      @
      // Post-conditions
      @ ensures      (high == low) ==> \result = lineOfActionnaires[low]; // cas de base
      @ ensures majoritaireSubArray1 != null && map.get(majoritaireSubArray1) > (high / 2) ==>
      @                                                     \result = map.get(majoritaireSubArray1);
      @ ensures majoritaireSubArray2 != null && map.get(majoritaireSubArray2) > (high/ 2)
                                        ==> \result = map.get(majoritaireSubArray2);
      @ ensures (majoritaireSubArray1 == null && map.get(majoritaireSubArray2) < high / 2) ==> \result = null;
      @ ensures (majoritaireSubArray2 == null && map.get(majoritaireSubArray1) < high / 2) ==> \result = null;
      @*/

    private static String getActionnaireMajoritaireDeLaLigne(String[] lineOfActionnaires,
                                                             int low, int high,
                                                             Map<String, Integer> map) {

        /* Comme le veux "diviser pour règner:  CAS DE BASE  */

        if ((high - low) == 0) {
            map.merge(lineOfActionnaires[low], 1, Integer::sum);
            return lineOfActionnaires[low];
        }

            /* Ensuite on divise la liste en 02 groupes et on trouve un possible
                      majoritaire dans chacun des groupes */
        int midpoint = (low + (high - low) / 2); // divide point
        String majoritaireSubArray1 = getActionnaireMajoritaireDeLaLigne(lineOfActionnaires, low,
                midpoint, map);

        String majoritaireSubArray2 = getActionnaireMajoritaireDeLaLigne(lineOfActionnaires,
                (midpoint + 1), high, map);

        int nbreOccMajo1 = Optional.ofNullable(majoritaireSubArray1).map(map::get).orElse(0);
        int nbreOccMajo2 = Optional.ofNullable(majoritaireSubArray2).map(map::get).orElse(0);

        if (nbreOccMajo1 > (high / 2)) return majoritaireSubArray1;
        if (nbreOccMajo2 > (high / 2)) return majoritaireSubArray2;
        return null;
    }/* ****************************** Fin Fonction utilisé dans problem_1************************* */


       /*
      @ requires s_file != null;
      // post-condition
      @ ensures \typeof(fileLinePb2[0]) == \type(Integer);
      @ ensures nbTests== 0 && totalLine == 0;
      @ ensures fileLinePb2.length>=3 ==> \result == result;
      @ ensure fileLinePb2[0] <=0 ==> \result==null;
      @*/

    /* ******* PROBLEM 2 NAIVE VERSION******************************************************************************* */
    public static String[] problem_2_naive(String s_file) {
        //System.out.println("===");
        //System.out.println(s_file);
        //System.out.println("===");

        if (s_file == null) {

            return null;
        }
         String[] fileLinesPb2 = /*new String[0];
        fileLinesPb2  = */s_file.split("\\r?\\n");


        if(fileLinesPb2.length < 0|| fileLinesPb2[0].length() > 2) {
            return null;
        }
        int nbTests;


        if (fileLinesPb2[0].equals("") || Integer.valueOf(fileLinesPb2[0]) < 1) {
            return null;
        } else {
            nbTests = Integer.parseInt(fileLinesPb2[0]);
        }
        int totalLine = fileLinesPb2.length;
        if (nbTests == 0) {
            return null;
        }


                nbTests  = Integer.parseInt(fileLinesPb2[0]);
        final String[] result = new String[nbTests];
        int addingTestCase = 0;


        totalLine--;

        /*@
          @ loop_invariant 0 <= entry && entry<= Integer.valueOf(fileLinePb2[0)] ;
          @ increasing entry + 1;
          @ modifies entry,result,addingTestCase, totalLine;
          @ decreasing  (totalLine + fileLinePb2[0]), ;
          @*/

        for (int entry = 0; entry < Integer.parseInt(fileLinesPb2[0]); entry++) {
            String[] dimension = fileLinesPb2[1 + addingTestCase].split(" ");
            if (' ' == fileLinesPb2[1 + addingTestCase].charAt(0)) {
                System.out.println(" erreur no 0");
                // return null;
            }
            int dimensionHeight = Integer.parseInt(dimension[0]);
            int dimensionWidth = Integer.parseInt(dimension[1]);

            if (totalLine - dimensionHeight < 0) {
                return null;
            }


            if (2 + addingTestCase + dimensionHeight < fileLinesPb2.length) {

                if (isItemOfTheMatrix(String.valueOf(fileLinesPb2[2 + addingTestCase + dimensionHeight].charAt(0)))) {
                    return null;
                }
            }

            if (dimensionHeight< 1 || dimensionWidth < 1) {
                return null;
            }


            String[][] matrix = new String[dimensionWidth][dimensionHeight];


            for (int y = 0; y < dimensionHeight; y++) {

                for (int x = 0; x < dimensionWidth; x++) {

                    if (fileLinesPb2[y +2+ addingTestCase].length() != dimensionWidth) {
                        return null;
                    }

                    if (isItemOfTheMatrix(Character.toString(fileLinesPb2[y + addingTestCase + 2].charAt(x)))) {
                        matrix[x][y] = Character.toString(fileLinesPb2[y + addingTestCase+ 2].charAt(x));
                    } else {

                        return null;
                    }
                }
            }


            int solutionForThatEntry = maxOfTrees(0, 0, "right", matrix, 0);
            result[entry] = Integer.toString(solutionForThatEntry);
            nbTests--;
            addingTestCase +=dimensionHeight+ 1;
            totalLine = totalLine - dimensionHeight- 1;


            if (totalLine == 0 && nbTests > 0 || nbTests == 0 && totalLine > 0) {
                System.out.println(" erreur no 1");
                return null;
            }
        }
        return result;
    }



    public static int maxOfTrees(int x, int y, String direction, String[][] matrix, int sumOfTreeByCaseMtrx) {
        int left, right, down;


        if (x < 0 || x > matrix.length || y > matrix[0].length || y < 0) {
            return -100000;
        }

        if (("T".equals(matrix[x][y]))) {
            sumOfTreeByCaseMtrx++;
        }

        if (isBlocked(x, y, matrix)) {
            return sumOfTreeByCaseMtrx;
        }


        switch (direction) {
            case "down":
                int downRL = 0;
                down = 0;
                if (canGoDown(x, y, matrix)) {
                    down = maxOfTrees(x, y + 1, "down", matrix, sumOfTreeByCaseMtrx);
                }

                if (y % 2 == 0 && canGoRight(x, y,matrix)) {
                    downRL = maxOfTrees(x + 1, y, "right", matrix, sumOfTreeByCaseMtrx);

                }
                if (y % 2 == 1 && canGoLeft(x, y, matrix)) {
                    downRL =maxOfTrees(x - 1, y, "left", matrix,sumOfTreeByCaseMtrx);
                }
                return Math.max(down, downRL);

            case "right":
                right = 0;
                down = 0;
                if (canGoRight(x, y,matrix)) {
                    right = maxOfTrees(x + 1, y, "right", matrix, sumOfTreeByCaseMtrx);
                }
                if (canGoDown(x, y,matrix)) {
                    down = maxOfTrees(x, y + 1, "down", matrix, sumOfTreeByCaseMtrx);
                }
                return (Math.max(right, down));
            case "left":
                left = 0;
                down = 0;
                if (canGoLeft(x, y, matrix)) {
                    left = maxOfTrees(x - 1, y, "left", matrix, sumOfTreeByCaseMtrx);
                if (canGoDown(x, y, matrix)) {
                }
                    down =maxOfTrees(x, y + 1, "down", matrix, sumOfTreeByCaseMtrx);
                }
                return (Math.max(left, down));
        }
        return -7000000;
    }

    public static boolean isBlocked(int x, int y, String[][] matrix) {
        if (x == 0 && y == 0 && ("#").equals(matrix[x][y])) {
            return true;
        }
        if (y % 2 == 0) {
            return !(canGoRight(x, y,matrix) || canGoDown(x, y, matrix));
        } else {
            return !(canGoLeft(x, y, matrix) || canGoDown(x, y,matrix));
        }
    }



    public static boolean canGoRight(int x, int y, String[][] matrix) {
        if (x + 1 >= matrix.length) {
            return false;
        }
        if (("#").equals(matrix[x + 1][y])) {
            return false;
        }
        return true;
    }


    public static boolean canGoLeft(int x, int y, String[][] matrix) {
        if (x - 1 < 0) {
            return false;
        }
        if (("#").equals(matrix[x - 1][y])) {
            return false;
        }
        return true;
    }


    public static boolean canGoDown(int x, int y, String[][] matrix) {

        if (y + 1 >= matrix[0].length) {
            return false;
        }
        if (("#").equals(matrix[x][y + 1])) {
            return false;
        }
        return true;
    }

    public static boolean isItemOfTheMatrix(String s) {

        return (("#").equals(s) || ("T").equals(s) || ("0").equals(s));
    } /* *************** fin problem 2naive *******************************************************   */


 /*@
      @ requires s_file != null;
      @requires fileLinePb2.length>=3 && dimension.length>0;
      @ ensures fileLinePb2= s_file.split("\n");
      @ ensures \typeof(fileLinePb2[0]) == \type(Integer);
      @ ensures nbOfTests == 0 ==> \result ==null;
      @*/


    /* ******* PROBLEM 2 Dynamic programming  VERSION*********************************************************************** */
    public static String[] problem_2(String s_file) {
        //System.out.println("====");
        // System.out.println(s_file);
        // System.out.println("====");
        // String[] s_tmp = {"8", "1", "3", "0"};
        //String[] s_tmp = null;

      //  System.out.println(""s_file);

        if (s_file == null) {
            System.out.println(" erreur no 0");
            return null;
        }

        final String[] fileLinePb2 = s_file.split("\r?\n");


        if (fileLinePb2[0].length() > 2 || fileLinePb2.length < 3) {
            System.out.println(" erreur no 1");
            return null;
        }
        int nbOfTests=0;
        if (("").equals(fileLinePb2[0]) || Integer.valueOf(fileLinePb2[0]) < 1) {
            //System.out.println(" erreur no 2");
            return null;
        }
            try {
                nbOfTests = Integer.parseInt(fileLinePb2[0]);
            } catch (NullPointerException e) {
                System.out.println(" erreur no 3");
              //  return null;
            }

        int totalLine = fileLinePb2.length;
            System.out.println("total lineeeeeee"+totalLine);
        if (nbOfTests == 0) {
            System.out.println(" erreur no 4");
            return null;
        }

        final String[] result = new String[nbOfTests];
        int lineOfTestCase = 0;
        boolean isFinish;
        totalLine--;

    //}catch(NullPointerException e ){
      //  return null;
    //}

   //try {


      for (int entry = 0; entry < nbOfTests; entry++) {
          int finalmaxOfTreesCut=0;
          isFinish = false;
          String[] dimensions = fileLinePb2[1 + lineOfTestCase].split(" ");
          System.out.println("lineeeeeee"+dimensions[0]+ " "+ dimensions[1]);

          if ((' ')==fileLinePb2[1 + lineOfTestCase].charAt(0) ) {
              System.out.println(" erreur no 5");
              return null;
          }

          int dimensionHeight = Integer.parseInt(dimensions[0]);
          int dimensionWidth = Integer.parseInt(dimensions[1]);

          if (totalLine < dimensionHeight) {
              System.out.println(" erreur no 6");
              return null;
          }


          if (1 + lineOfTestCase + dimensionHeight > fileLinePb2.length) {
              System.out.println(" erreur no 7");
              return null;
          }
          if ((2 + lineOfTestCase + dimensionHeight ) < fileLinePb2.length) {
              if (isItemOfTheMatrix((String.valueOf(fileLinePb2[2 + lineOfTestCase + dimensionHeight].charAt(0))))) {
                  System.out.println(" erreur no 8.0");
                  return null;
              }
          }
          if (dimensionHeight < 1 || dimensionWidth < 1) {
              System.out.println(" erreur no 8");
              return null;
          }

          String[][] matrix = new String[dimensionWidth][dimensionHeight];
          int[][] maxOfTheBox = new int[dimensionWidth][dimensionHeight];
          boolean[][] reachability = new boolean[dimensionWidth][dimensionHeight];

          for (int y = 0; y < dimensionHeight; y++) {
              int maxTreesOfTwo;
              if (isFinish) {
//                  break;
              }

              if (y % 2 == 0) {
                  for (int x = 0; x < dimensionWidth; x++) {
                      if (fileLinePb2[y +lineOfTestCase + 2].length() != dimensionWidth) {
                          System.out.println(" erreur no 9");
                          return null;
                      }
                      matrix[x][y] = Character.toString((fileLinePb2[y + lineOfTestCase + 2]).charAt(x));

                      maxTreesOfTwo = Math.max(maxFromLeft(matrix, x, y, maxOfTheBox),
                              maxFromUp(matrix, x, y, maxOfTheBox));

                      if (isTheFirstBox(x, y)) {
                            if((("#").equals(matrix[x][y]))){
                              result[entry] = "0";
                              isFinish = true;
                              break;
                            }
                      }
                      if (!isItemOfTheMatrix(matrix[x][y])) {
                          System.out.println(" erreur no 10");
                          return null;
                      }
                      if (("#").equals(matrix[x][y])) {
                          reachability[x][y] = false;
                          maxOfTheBox[x][y] = 0;
                      } else if (("T").equals(matrix[x][y])) {
                          if (!isTheFirstBox(x, y) && (!isBlockedFromUp(matrix, x, y, reachability) ||
                                  !isBlockedFromLeft(matrix, x, y, reachability))) {
                              maxOfTheBox[x][y] = maxTreesOfTwo + 1;
                              reachability[x][y] = true;
                          } else {

                              maxOfTheBox[x][y] = 0;
                              reachability[x][y] = false;
                          }

                          if (isTheFirstBox(x, y)) {

                              maxOfTheBox[x][y] = 1;
                              reachability[x][y] = true;
                          }
                      } else {
                          maxOfTheBox[x][y] = maxTreesOfTwo;
                          reachability[x][y] = true;
                      }
                      if (!isTheFirstBox(x, y) && isBlockedFromUp(matrix, x, y, reachability) &&
                              isBlockedFromLeft(matrix, x, y, reachability)) {
                          reachability[x][y] = false;
                      }
                      if (finalmaxOfTreesCut < maxOfTheBox[x][y]) {
                          finalmaxOfTreesCut = maxOfTheBox[x][y];
                      }
                  }

              }
              /* ******************************************LIGNE IMPAIRE ********************************************* */
              else {

                  for(int x = (dimensionWidth - 1); x >= 0; x--) {
                      if (fileLinePb2[y + lineOfTestCase + 2].length() != dimensionWidth) {
                          System.out.println(" erreur no 11");
                          return null;
                      }

                      matrix[x][y] = Character.toString(fileLinePb2[y + 2 + lineOfTestCase].charAt(x));

                      maxTreesOfTwo = Math.max(maxFromRight(matrix, x, y, maxOfTheBox), maxFromUp(matrix, x, y,
                              maxOfTheBox));

                      if (!isItemOfTheMatrix(matrix[x][y])) {
                          System.out.println(" erreur no 12");
                          return null;
                      }

                      if (("#").equals(matrix[x][y])) {
                          maxOfTheBox[x][y] = 0;
                          reachability[x][y] = false;
                      } else if (("T").equals(matrix[x][y])) {
                          if ((!isBlockedFromUp(matrix, x, y, reachability) ||
                                  !isBlockedFromRight(matrix, x, y, reachability))) {

                              maxOfTheBox[x][y] = maxTreesOfTwo + 1;
                              reachability[x][y] = true;
                          } else {
                              maxOfTheBox[x][y] = 0;
                              reachability[x][y] = false;
                          }
                      } else {
                          maxOfTheBox[x][y] = maxTreesOfTwo;
                          reachability[x][y] = true;
                      }
                      if (!isTheFirstBox(x, y) && isBlockedFromUp(matrix, x, y, reachability) &&
                              isBlockedFromRight(matrix, x, y, reachability)) {
                          reachability[x][y] = false;
                          //maxOfTheBox[x][y] = 0;
                      }
                      if (finalmaxOfTreesCut < maxOfTheBox[x][y]) {
                          finalmaxOfTreesCut = maxOfTheBox[x][y];

                      }
                  }
              }
          }
         // System.out.println("matrixxxx "+matrix[0][0]);

          if (!isFinish) {
              result[entry] = Integer.toString(finalmaxOfTreesCut);
          }
          nbOfTests--;
          lineOfTestCase += dimensionHeight + 1;
          totalLine = totalLine - dimensionHeight - 1;
          if ((totalLine == 0)&& nbOfTests > 0  ) {
              System.out.println(" erreur no 13");
             return null;
          }
      }

      return result;

    }/******************************fin problem 2 programmation dynamique ********************************************  */


    public static int maxFromLeft(String[][] matrix, int x,int y,int[][] maxOfTheBox){
        if(x==0) {
            return 0;
        }
        else if(("#").equals(matrix[x-1][y])) {
            return 0;
        } else{
            return maxOfTheBox[x-1][y];
        }
    }
    public static  int maxFromRight(String[][] matrix, int x,int y, int[][] maxOfTheBox){
        if(x==matrix.length-1) {
            return 0;
        }
        else if (("#").equals(matrix[x + 1][y])) {
            return 0;
        } else {
            return maxOfTheBox[x + 1][y];
        }
    }

    public static int maxFromUp(String[][] matrix, int x,int y,int[][] maxOfTheBox ){
        if(y==0) {
            return 0;
        }
        else if(("#").equals(matrix[x][y-1])){
        return 0;
        }
        else {
            return maxOfTheBox[x][y-1];
        }
    }
    public static boolean isBlockedFromUp(String[][]matrix,int x,int y, boolean[][] reachability){
        if(y==0){
            return true;
        }
        if(("#").equals(matrix[x][y-1])) {
            return true;
        }
        if(reachability[x][y-1]) {
            return false;
        }
        else{
            return true;
        }
    }
    public static boolean isBlockedFromLeft(String[][]matrix,int x,int y, boolean[][] reachability){
        if(x==0){
            return true;
        }
        if(("#").equals(matrix[x-1][y])) {
            return true;
        }
        if(reachability[x-1][y]) {
            return false;
        }
        else {
            return  true;
        }
    }

    public static boolean isBlockedFromRight(String[][] matrix,int x, int y, boolean[][] reachability) {

        if (x == (matrix.length-1)) {
            return true;
        }
        if (("#").equals(matrix[x + 1][y])) {
            return true;
        }
        if (reachability[x + 1][y]) {
            return false;
        } else{
            return true;
        }
    }


    public  static boolean isTheFirstBox(int x, int y){
        if(x==0 && y==0) {
            return true;
        }
        else {
            return false;
       }

}


    /* ******* PROBLEM 3 NAIVE VERSION*********************************************************************************** */
           /*
             @requires d.size()>0;
             @requires (int i>=0 && i<t)==> d.get(i).size()>=2 && d.get(i).size()<=100  ;
            // post-condition
             @ ensures \typeof(d.get(i)) == \type(Integer);
             @ ensures (d.get(i).size()>=2 &&d.get(i).size()<=100) ==> \result == result;
            * */
    public static String[] problem_3_naive(String s_file) {
        System.out.println("===");
        System.out.println(s_file);
        System.out.println("===");
        String[] s_tmp = {"1", "0", "1", "1"};
        //String[] s_tmp = null;
        // String[] s_tmp = {"null1","null2", "null3","null4"};
        try {
            readData(s_file);
        }catch(Exception e){
            e.printStackTrace();
            return null;

        }
        String[] result =new String[t];
        for (int i=0;i<t;i++){

            result[i] = String.valueOf(greedyNaive(N.get(i), d.get(i)));
          //  result[i]=""+greedyNaive(N.get(i), d.get(i));


        }

            System.out.println("naive Solution for problem3 :");
            for(String s:result)
            System.out.print(s+" ");

        return  result;
        //return s_tmp;
    }


                /* **************** a naive greedy to use in problem3 naive ************************ */
    static int greedyNaive(int Ni, List<Integer> di){
                Comparator<Integer> comparator = Comparator.reverseOrder();
                 di.sort(comparator);
                 int total = 0;
                 for(int node=0;node<Ni;node++) {

                     int friendMax;
                     friendMax = di.get(0);
                     for (int friend = 1; friend <= friendMax; friend++) {
                         if (di.get(friend) < 1)
                             return 0;
                         else
                             di.set(friend, (di.get(friend) - 1));
                     }
                     di.remove(0);
                     di.sort(comparator);

                     if (di.get(0) == 0)
                         return 1;
                     if (di.get(0) == 1) {
                         for (int remainingFriend : di)
                             total = total + remainingFriend;
                         if (total % 2 == 0)
                             return 1;
                         else
                             return 0;
                     }

                 }
        return 0;
    }


     static void readData(String fileData) throws Exception {
         fileLines= new String[0];
         N = new ArrayList< Integer>();
         d = new ArrayList<List<Integer>>();
        fileLines = fileData.split("\\r?\\n");
        if (fileLines.length%2 == 0){
            throw new Exception(" Incorrect: the number of line in the file !"+fileLines.length);
        }

        String str = new String();
        int ini; // initial position
        int fin;  // final position

         int  number= 1;
        try {
            t = Integer.parseInt(fileLines[0].trim());

            for (int i = 1; i <= t; i++)
                d.add(new ArrayList<Integer>());
            for (int i = 0; i < t; i++) {
                while ((str = fileLines[number].trim()) == null || str.equals("")) {
                    // do nothing
                }
                number++;
                N.add(Integer.parseInt(str.trim()));
                while ((str = fileLines[number].trim()) == null || str.equals("")) {
                    // do nothing
                }
                number++;
                ini = 0;
                    if (N.get(i)<2||N.get(i)>1000){
                        throw new Exception("Error: a friends'range should be beetween  2 to 1000 !" );
                    }

                for (int j = 1; j <= N.get(i); j++) { //position in d[i]
                    if (j != N.get(i))
                        fin = str.indexOf(" ", ini);
                    else
                        fin = str.length();
                    if ((Integer.parseInt(str.substring(ini, fin).trim())) >N.get(i)) {
                    //    System.out.println("Error, degree >=" + N.get(i));
                        throw new Exception("Error: Degree >= "+ N.get(i));

                    }
                    d.get(i).add(Integer.parseInt(str.substring(ini, fin).trim()));
                    ini = fin + 1;
                }
                for(int node :d.get(i) ){
                    if (node <1||node >d.get(i).size()){
                        throw new Exception("Error:  total connection for a friend is wrong ! ");
                    }
                }

            }
        } catch (Exception e) {
            System.err.println("Incorrect format number  at line: " +number);

        }

    }


    /* ******* PROBLEM 3 ************************************************************** */
    /*
     @requires d.size()>0;
    //post-condition
     @requires(\forall int i,j; 0<=i,j && i<t && j< d.get(i).size()==> d.get(i).get(j)>=0)// un degré est positif
    @ensures N.get(i)>0 && d.get(i).size()>2 ==> \result==result;

    * */


   public static String[] problem_3(String s_file) {
      /*  System.out.println("===");
        System.out.println(s_file);
        System.out.println("===");
       */ //String[] s_tmp = {"1", "0", "1", "1"};
        //String[] s_tmp = null;
           try {
               readData(s_file);
           }catch (Exception e){
               e.printStackTrace();
               return null;
           }
            String[] result = new String[t];
            for (int i=0 ;i <t; i++){
                result[i] = String.valueOf(greedySmart(N.get(i),d.get(i)));

            }
                System.out.println(" solution problem3 using greedy's proprieties: ");
                for(String s:result)
                 System.out.print(s+" ");
                System.out.println();

       return result;

   }

    /* ***************** use greedy technic to solve  problem 3*********************************** */
    public static int greedySmart(int Ni, List<Integer> di ){
        Comparator<Integer> comparator = Collections.reverseOrder();
        di.sort(comparator);
        int total = 0;

        if(di.get(0)==0)
            return 1;
        if (di.get(0)==1){
            for(int remainingFriends: di)
                total = total + remainingFriends;
            if (total%2==0)
                return 1;
            else
                return 0;
        }

        int friendMaxCurrent = di.get(0);

        for(int friend=1;friend <=friendMaxCurrent;friend++){
            if(di.get(friend) <1)
                return 0;
            else
                di.set(friend, di.get(friend)-1);
        }

        di.remove(0);

        List<Integer> remainingDegree = new ArrayList<Integer>(di);

        return greedySmart( Ni,remainingDegree);

    }

}
