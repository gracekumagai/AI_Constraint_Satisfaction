#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete the warehouse domain.  

'''
Construct and return Tenner Grid CSP models.
'''

from cspbase import *
import itertools

def tenner_csp_model_1(initial_tenner_board):
    '''Return a CSP object representing a Tenner Grid CSP problem along 
       with an array of variables for the problem. That is return

       tenner_csp, variable_array

       where tenner_csp is a csp representing tenner grid using model_1
       and variable_array is a list of lists

       [ [  ]
         [  ]
         .
         .
         .
         [  ] ]

       such that variable_array[i][j] is the Variable (object) that
       you built to represent the value to be placed in cell i,j of
       the Tenner Grid (only including the first n rows, indexed from 
       (0,0) to (n,9)) where n can be 3 to 8.
       
       
       The input board is specified as a pair (n_grid, last_row). 
       The first element in the pair is a list of n length-10 lists.
       Each of the n lists represents a row of the grid. 
       If a -1 is in the list it represents an empty cell. 
       Otherwise if a number between 0--9 is in the list then this represents a 
       pre-set board position. E.g., the board
    
       ---------------------  
       |6| |1|5|7| | | |3| |
       | |9|7| | |2|1| | | |
       | | | | | |0| | | |1|
       | |9| |0|7| |3|5|4| |
       |6| | |5| |0| | | | |
       ---------------------
       would be represented by the list of lists
       
       [[6, -1, 1, 5, 7, -1, -1, -1, 3, -1],
        [-1, 9, 7, -1, -1, 2, 1, -1, -1, -1],
        [-1, -1, -1, -1, -1, 0, -1, -1, -1, 1],
        [-1, 9, -1, 0, 7, -1, 3, 5, 4, -1],
        [6, -1, -1, 5, -1, 0, -1, -1, -1,-1]]
       
       
       This routine returns model_1 which consists of a variable for
       each cell of the board, with domain equal to {0-9} if the board
       has a 0 at that position, and domain equal {i} if the board has
       a fixed number i at that cell.
       
       model_1 contains BINARY CONSTRAINTS OF NOT-EQUAL between
       all relevant variables (e.g., all pairs of variables in the
       same row, etc.).
       model_1 also constains n-nary constraints of sum constraints for each 
       column.
    '''
    dom = []

    n_grid = initial_tenner_board[0]  #len n
    last_row = initial_tenner_board[1]  #row the represents sum
    #Transpose n_grid and variable_array to create lists representing columns
    n_grid_T = [list(i) for i in zip(*n_grid)]  #Transpose of n_grid - len 10

    #Init domain
    for i in range(10):
      dom.append(i)

    #Init var array
    variable_array = [[] for i in range(len(n_grid))]  

    #Init variables
    for i in range(len(n_grid)):
      for j in range(len(n_grid[i])):
        if n_grid[i][j] == -1:
          variable_array[i].append(Variable('V{},{}'.format(i,j), dom))
        else:
          variable_array[i].append(Variable('V{},{}'.format(i,j), [n_grid[i][j]]))

    #Add variables to the model
    vars = []
    for row in variable_array:
      for var in row:
        vars.append(var)

    #Create model
    tenner_csp = CSP("Vars", vars)

    #BINARY ROW CONSTRAINTS
    for row in range(len(n_grid)):
      #Iterate over length 2 tuples that represent all of the binary combinations in rows -- with repeats
      for binary in itertools.combinations(variable_array[row], 2):
        add_constraints_binary(binary, tenner_csp)


      #CONTIGUOUS CONSTRAINTS - COL AND DIAGONAL
      #Note: Already account for values in same row to be different, check corners, edges and cols
      for col in range(len(n_grid_T)):
        #Row Cases:
        if row == 0:
          #Corner Case: Top Left
          if col == 0:
            con = [variable_array[row+1][col+1], variable_array[row+1][col]]
          #Corner Case: Top Right
          elif col == (len(n_grid_T)-1):
            con = [variable_array[row+1][col-1],  variable_array[row+1][col]]
          #Edge Case: Top Row
          else:
            con = [variable_array[row+1][col-1], variable_array[row+1][col+1], variable_array[row+1][col]]
        elif row == (len(n_grid)-1):
          #Corner Case: Bottom Left
          if col == 0:
            con = [variable_array[row-1][col+1], variable_array[row-1][col]]
          #Corner Case: Bottom Right
          elif col == (len(n_grid_T)-1):
            con = [variable_array[row-1][col-1], variable_array[row-1][col]]
          #Edge Case: Bottom Row
          else:
            con = [variable_array[row-1][col-1], variable_array[row-1][col+1], variable_array[row-1][col]]
        elif col == 0:
          #Edge Case: Left Col
          con = [variable_array[row+1][col+1], variable_array[row-1][col+1], variable_array[row-1][col], variable_array[row+1][col]]
        elif col == (len(n_grid_T)-1):
          #Edge Case: Right Col
          con = [variable_array[row-1][col-1], variable_array[row+1][col-1], variable_array[row-1][col], variable_array[row+1][col]]
        else:
          #Not Edge or Corner: Position has 4 diagonal neighbors, 2 col neighbors
          con = [variable_array[row-1][col-1], variable_array[row-1][col+1], variable_array[row+1][col+1], variable_array[row+1][col-1], variable_array[row-1][col], variable_array[row+1][col]]
        
        #Add the current item and its neighbor to the csp's constraints
        for var in con:
          binary = [variable_array[row][col], var]
          add_constraints_binary(binary, tenner_csp)


    #SUM CONSTRAINT
    for col in range(len(n_grid_T)):
      desired = last_row[col]
      opt = []
      for row in range(len(n_grid)):
        if n_grid_T[col][row] == -1:
          opt.append(variable_array[row][col])
        else:
          #If value is pre-assigned, subtract this value from desired
          desired -= n_grid_T[col][row]

      varDoms = []
      for var in opt:
        varDoms.append(var.domain())

      #Find satisfying tuples and add to constraint list
      sat_tuples = []
      for t in itertools.product(*varDoms):
        if sum(t) == desired:  #Require unknown values to equal desired sum
          sat_tuples.append(t)

      con = Constraint('C:Sum_Col{}'.format(col), opt)
      con.add_satisfying_tuples(sat_tuples)
      tenner_csp.add_constraint(con)


    return tenner_csp, variable_array



def tenner_csp_model_2(initial_tenner_board):
    '''Return a CSP object representing a Tenner Grid CSP problem along 
       with an array of variables for the problem. That is return

       tenner_csp, variable_array

       where tenner_csp is a csp representing tenner using model_1
       and variable_array is a list of lists

       [ [  ]
         [  ]
         .
         .
         .
         [  ] ]

       such that variable_array[i][j] is the Variable (object) that
       you built to represent the value to be placed in cell i,j of
       the Tenner Grid (only including the first n rows, indexed from 
       (0,0) to (n,9)) where n can be 3 to 8.

       The input board takes the same input format (a list of n length-10 lists
       specifying the board as tenner_csp_model_1.
    
       The variables of model_2 are the same as for model_1: a variable
       for each cell of the board, with domain equal to {0-9} if the
       board has a -1 at that position, and domain equal {i} if the board
       has a fixed number i at that cell.

       However, model_2 has different constraints. In particular,
       model_2 has a combination of n-nary 
       all-different constraints and binary not-equal constraints: all-different 
       constraints for the variables in each row, binary constraints for  
       contiguous cells (including diagonally contiguous cells), and n-nary sum 
       constraints for each column. 
       Each n-ary all-different constraint has more than two variables (some of 
       these variables will have a single value in their domain). 
       model_2 should create these all-different constraints between the relevant 
       variables.
    '''

#IMPLEMENT

    dom = []

    n_grid = initial_tenner_board[0]  #len n
    last_row = initial_tenner_board[1]
    #Transpose n_grid and variable_array to create lists representing columns
    n_grid_T = [list(i) for i in zip(*n_grid)]  #Transpose of n_grid - len 10

    #Init domain <0, 9>
    for i in range(10):
      dom.append(i)

    #Init var array
    variable_array = [[] for i in range(len(n_grid))]  

    #Init variables
    for i in range(len(n_grid)):
      for j in range(len(n_grid[i])):
        if n_grid[i][j] == -1:
          variable_array[i].append(Variable('V{},{}'.format(i,j), dom))
        else:
          variable_array[i].append(Variable('V{},{}'.format(i,j), [n_grid[i][j]]))

    #Add variables to the model
    vars = []
    for row in variable_array:
      for var in row:
        vars.append(var)

    #Create model
    tenner_csp = CSP("Vars", vars)
    
    #ALL DIFFERENT ROW CONSTRAINT
    for row in range(len(n_grid)):
      opt = []
      varDoms = list(dom)
      for col in range(len(n_grid_T)):
        if n_grid[row][col] == -1:
          opt.append(variable_array[row][col])
        else:
          #Remove pre-assigned values from the domain to be considered
          if n_grid[row][col] in varDoms:
            varDoms.remove(n_grid[row][col])

      #Find satisfying tuples and add to constraint list
      sat_tuples = []
      for t in itertools.permutations(varDoms, len(opt)):
          sat_tuples.append(t)

      con = Constraint('C:Row{}'.format(col), opt)
      con.add_satisfying_tuples(sat_tuples)
      tenner_csp.add_constraint(con)  
    
      #CONTIGUOUS CONSTRAINTS - COL AND DIAGONAL
      #Note: Already account for values in same row to be different, check corners, edges and cols
      for col in range(len(n_grid_T)):
        #Row Cases:
        if row == 0:
          #Corner Case: Top Left
          if col == 0:
            con = [variable_array[row+1][col+1], variable_array[row+1][col]]
          #Corner Case: Top Right
          elif col == (len(n_grid_T)-1):
            con = [variable_array[row+1][col-1],  variable_array[row+1][col]]
          #Edge Case: Top Row
          else:
            con = [variable_array[row+1][col-1], variable_array[row+1][col+1], variable_array[row+1][col]]
        elif row == (len(n_grid)-1):
          #Corner Case: Bottom Left
          if col == 0:
            con = [variable_array[row-1][col+1], variable_array[row-1][col]]
          #Corner Case: Bottom Right
          elif col == (len(n_grid_T)-1):
            con = [variable_array[row-1][col-1], variable_array[row-1][col]]
          #Edge Case: Bottom Row
          else:
            con = [variable_array[row-1][col-1], variable_array[row-1][col+1], variable_array[row-1][col]]
        elif col == 0:
          #Edge Case: Left Col
          con = [variable_array[row+1][col+1], variable_array[row-1][col+1], variable_array[row-1][col], variable_array[row+1][col]]
        elif col == (len(n_grid_T)-1):
          #Edge Case: Right Col
          con = [variable_array[row-1][col-1], variable_array[row+1][col-1], variable_array[row-1][col], variable_array[row+1][col]]
        else:
          #Not Edge or Corner: Position has 4 diagonal neighbors, 2 col neighbors
          con = [variable_array[row-1][col-1], variable_array[row-1][col+1], variable_array[row+1][col+1], variable_array[row+1][col-1], variable_array[row-1][col], variable_array[row+1][col]]
        
        #Add the current item and its neighbor to the csp's constraints
        for var in con:
          binary = [variable_array[row][col], var]
          add_constraints_binary(binary, tenner_csp)


    #SUM CONSTRAINT
    for col in range(len(n_grid_T)):
      desired = last_row[col]
      opt = []
      for row in range(len(n_grid)):
        if n_grid_T[col][row] == -1:
          opt.append(variable_array[row][col])
        else:          
          #If value is pre-assigned, subtract this value from desired
          desired -= n_grid_T[col][row]

      varDoms = []
      for var in opt:
        varDoms.append(var.domain())

      #Find satisfying tuples and add to constraint list
      sat_tuples = []
      for t in itertools.product(*varDoms):
        if sum(t) == desired:  #Require unknown values to equal desired sum
          sat_tuples.append(t)

      con = Constraint('C:Sum_Col{}'.format(col), opt)
      con.add_satisfying_tuples(sat_tuples)
      tenner_csp.add_constraint(con)

    return tenner_csp, variable_array

def add_constraints_binary(combos, csp):
    '''This function adds constraints from the given pair passed in through the 
    argument combo and adds the constraint to the given csp
    '''
    con = Constraint('C:V{}xV{}'.format(combos[0].name, combos[1].name), combos)

    varDoms = []
    for var in combos:
      varDoms.append(var.domain())

    #Find satisfying tuples and add to constraint list
    sat_tuples = []
    for t in itertools.product(*varDoms):
      if t[0] != t[1]:  #Tuple can not represent the same value twice!
        sat_tuples.append(t)

    con.add_satisfying_tuples(sat_tuples)
    csp.add_constraint(con)