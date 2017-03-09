#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete problem solution.  

'''This file will contain different constraint propagators to be used within 
   bt_search.

   propagator == a function with the following template
      propagator(csp, newVar=None)
           ==> returns (True/False, [(Variable, Value), (Variable, Value) ...]

      csp is a CSP object---the propagator can use this to get access
      to the variables and constraints of the problem. The assigned variables
      can be accessed via methods, the values assigned can also be accessed.

      newVar (newly instaniated variable) is an optional argument.
      if newVar is not None:
          then newVar is the most
           recently assigned variable of the search.
      else:
          progator is called before any assignments are made
          in which case it must decide what processing to do
           prior to any variables being assigned. SEE BELOW

       The propagator returns True/False and a list of (Variable, Value) pairs.
       Return is False if a deadend has been detected by the propagator.
       in this case bt_search will backtrack
       return is true if we can continue.

      The list of variable values pairs are all of the values
      the propagator pruned (using the variable's prune_value method). 
      bt_search NEEDS to know this in order to correctly restore these 
      values when it undoes a variable assignment.

      NOTE propagator SHOULD NOT prune a value that has already been 
      pruned! Nor should it prune a value twice

      PROPAGATOR called with newVar = None
      PROCESSING REQUIRED:
        for plain backtracking (where we only check fully instantiated 
        constraints) 
        we do nothing...return true, []

        for forward checking (where we only check constraints with one
        remaining variable)
        we look for unary constraints of the csp (constraints whose scope 
        contains only one variable) and we forward_check these constraints.

        for gac we establish initial GAC by initializing the GAC queue
        with all constaints of the csp


      PROPAGATOR called with newVar = a variable V
      PROCESSING REQUIRED:
         for plain backtracking we check all constraints with V (see csp method
         get_cons_with_var) that are fully assigned.

         for forward checking we forward check all constraints with V
         that have one unassigned variable left

         for gac we initialize the GAC queue with all constraints containing V.
   '''

def prop_BT(csp, newVar=None):
    '''Do plain backtracking propagation. That is, do no 
    propagation at all. Just check fully instantiated constraints'''
    
    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 0:
            vals = []
            vars = c.get_scope()
            for var in vars:
                vals.append(var.get_assigned_value())
            if not c.check(vals):
                return False, []
    return True, []

def prop_FC(csp, newVar=None):
    '''Do forward checking. That is check constraints with 
       only one uninstantiated variable. Remember to keep 
       track of all pruned variable,value pairs and return '''
#IMPLEMENT
    
    pruned_ls = []

    if not newVar:
      #we look for unary constraints of the csp (constraints whose scope 
      #contains only one variable) and we forward_check these constraints.
      for c in csp.get_all_cons():
        scope = c.get_scope()
        if len(scope) == 1 and c.get_n_unasgn() == 1: #and unassigned?
          unasgn_vars = c.get_unasgn_vars();

          DWOccurred, pruned_ls = FCCheck(c, unasgn_vars[0], pruned_ls)

          if not DWOccurred:
            return False, pruned_ls      

      return True, pruned_ls

    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 1:
            unasgn_vars = c.get_unasgn_vars();

            DWOccurred, pruned_ls = FCCheck(c, unasgn_vars[0], pruned_ls)

            if not DWOccurred:
              return False, pruned_ls            

    return True, pruned_ls
  
def FCCheck(c, x, pruned_ls):
  ''' C is a constraint with all its variables already assigned, except
  for variable X'''
  vals = []
  vars = c.get_scope()

  for var in vars:
    vals.append(var.get_assigned_value())
  
  for index, val in enumerate(vals, start=0):
    if val == None:
      unasgn_index = index
    
  for val in x.cur_domain():
    vals[unasgn_index] = val
    if not c.check(vals):
      x.prune_value(val)
      pruned_ls.append(tuple((x, val)))
  
  if x.cur_domain_size() == 0:
    return False, pruned_ls
  
  return True, pruned_ls


def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce 
       processing all constraints. Otherwise we do GAC enforce with
       constraints containing newVar on GAC Queue'''
#IMPLEMENT
    GACQueue = Queue()
    pruned_ls = []

    if newVar == None:
        #for gac we establish initial GAC by initializing the GAC queue
        #with all constaints of the csp
        for c in csp.get_all_cons():
          GACQueue.enqueue(c)
        DWOccurred, pruned_ls = GAC_Enforce(csp, GACQueue, pruned_ls)

        if not DWOccurred:
          return False, pruned_ls
        
        return True, pruned_ls

    #Prune all values of newVar that are not equal to its assigned value
    for val in newVar.cur_domain():
      if val != newVar.get_assigned_value():
        pruned_ls.append(tuple((newVar, val)))
        newVar.prune_value(val)

      for c in csp.get_cons_with_var(newVar):
          GACQueue.enqueue(c)

      DWOccurred, pruned_ls = GAC_Enforce(csp, GACQueue, pruned_ls)
      if not DWOccurred:
        for p_val in newVar.domain():
          if p_val not in newVar.cur_domain():
            newVar.unprune_value(p_val)

        return False, pruned_ls

    return True, pruned_ls


def GAC_Enforce(csp, q, pruned_ls):
  ''' GAC-Queue contains all constraints one of whose variables has
  had its domain reduced. At the root of the search tree
  first we run GAC_Enforce with all constraints on GAC-Queue '''

  while not q.isEmpty():
    c = q.dequeue()
    for var in c.get_scope():
      for val in var.cur_domain():

        if not c.has_support(var, val):
          var.prune_value(val)
          pruned_ls.append(tuple((var, val)))

          #When CurDom of variable is empty
          if var.cur_domain_size() == 0:
            while not q.isEmpty():
              q.dequeue() #Empty GACQueue
            return False, pruned_ls
          else:
            #push all constraints C' st var is in scope(C') and C' is not in
            #GACQueue onto GACQueue
            for con in csp.get_cons_with_var(var):
              if not q.accountedFor(con):
                q.enqueue(con)

  return True, pruned_ls



class Queue:
  def __init__(self):
    self.items = []

  def isEmpty(self):
    #Check if queue is empty
    return self.items == []
  
  def enqueue(self, item):
    #Adds item to end of queue
    rear = len(self.items) + 1
    self.items.insert(rear, item)
  
  def dequeue(self):
    #Removes 1st item in the list
    if self.isEmpty():
      print("ERROR: Queue is empty")
    else:
      return self.items.pop(0)  

  def insert_front(self, item):
    #Adds item to start of queue
    self.items.insert(0, item)

  def size(self):
    #Returns size of queue
    return len(self.items)
  
  def printqueue(self):
      print(self.items)
  
  def getQueue(self):
    #returns list representing queue
    return self.items

  def emptyQueue(self):
    #delete all items in queue
    while not self.isEmpty():
      self.dequeue()
    
  def accountedFor(self, item):
    #check if item is in queue
    return item in self.items
