import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
   def __init__(self, facts=[], rules=[]):
       self.facts = facts
       self.rules = rules
       self.ie = InferenceEngine()

   def __repr__(self):
       return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

   def __str__(self):
       string = "Knowledge Base: \n"
       string += "\n".join((str(fact) for fact in self.facts)) + "\n"
       string += "\n".join((str(rule) for rule in self.rules))
       return string

   def _get_fact(self, fact):
       """INTERNAL USE ONLY
       Get the fact in the KB that is the same as the fact argument

       Args:
           fact (Fact): Fact we're searching for

       Returns:
           Fact: matching fact
       """
       for kbfact in self.facts:
           if fact == kbfact:
               return kbfact

   def _get_rule(self, rule):
       """INTERNAL USE ONLY
       Get the rule in the KB that is the same as the rule argument

       Args:
           rule (Rule): Rule we're searching for

       Returns:
           Rule: matching rule
       """
       for kbrule in self.rules:
           if rule == kbrule:
               return kbrule

   def kb_add(self, fact_rule):
       """Add a fact or rule to the KB
       Args:
           fact_rule (Fact|Rule) - the fact or rule to be added
       Returns:
           None
       """
       printv("Adding {!r}", 1, verbose, [fact_rule])
       if isinstance(fact_rule, Fact):
           if fact_rule not in self.facts:
               self.facts.append(fact_rule)
               for rule in self.rules:
                   self.ie.fc_infer(fact_rule, rule, self)
           else:
               if fact_rule.supported_by:
                   ind = self.facts.index(fact_rule)
                   for f in fact_rule.supported_by:
                       self.facts[ind].supported_by.append(f)
               else:
                   ind = self.facts.index(fact_rule)
                   self.facts[ind].asserted = True
       elif isinstance(fact_rule, Rule):
           if fact_rule not in self.rules:
               self.rules.append(fact_rule)
               for fact in self.facts:
                   self.ie.fc_infer(fact, fact_rule, self)
           else:
               if fact_rule.supported_by:
                   ind = self.rules.index(fact_rule)
                   for f in fact_rule.supported_by:
                       self.rules[ind].supported_by.append(f)
               else:
                   ind = self.rules.index(fact_rule)
                   self.rules[ind].asserted = True

   def kb_assert(self, fact_rule):
       """Assert a fact or rule into the KB

       Args:
           fact_rule (Fact or Rule): Fact or Rule we're asserting
       """
       printv("Asserting {!r}", 0, verbose, [fact_rule])
       self.kb_add(fact_rule)

   def kb_ask(self, fact):
       """Ask if a fact is in the KB

       Args:
           fact (Fact) - Statement to be asked (will be converted into a Fact)

       Returns:
           listof Bindings|False - list of Bindings if result found, False otherwise
       """
       print("Asking {!r}".format(fact))
       if factq(fact):
           f = Fact(fact.statement)
           bindings_lst = ListOfBindings()
           # ask matched facts
           for fact in self.facts:
               binding = match(f.statement, fact.statement)
               if binding:
                   bindings_lst.add_bindings(binding, [fact])

           return bindings_lst if bindings_lst.list_of_bindings else []
          
       else:
           print("Invalid ask:", fact.statement)
           return []


   def kb_explain(self, fact_or_rule):
        """
        Explain where the fact or rule comes from

        Args:
            fact_or_rule (Fact or Rule) - Fact or rule to be explained

        Returns:
            string explaining hierarchical support from other Facts and rules
        """
        ####################################################
        # Student code goes here

        def kb_explain_recursive(self, fact_or_rule, indexer):
            tab = indexer * "    " 
            answer = ""
            if isinstance(fact_or_rule, Rule):
                answer += tab + "rule: " 
                x = 1
                nad = len(fact_or_rule.lhs)
                for y in fact_or_rule.lhs:
                    if x == len(fact_or_rule.lhs):
                        if x == 1:
                            answer += "("+str(y)+")"
                        else:
                            answer += ""+str(y)+")"
                    else:
                        if x == 1:
                            answer += "("+str(y)+", "
                        else:
                            answer += ""+str(y)+", "
                    x = x + 1
                answer += " -> " + str(fact_or_rule.rhs)
                if fact_or_rule.asserted == True:
                    answer += " ASSERTED\n"
                    return answer
                else:
                    answer += "\n"
                    for support in fact_or_rule.supported_by:
                        answer += tab + "  SUPPORTED BY\n"
                        for supporter in support:
                            answer += kb_explain_recursive(self, supporter, indexer + 1)
                    return answer
            if isinstance(fact_or_rule, Fact):
                answer += tab + "fact: " + str(fact_or_rule.statement)
                if fact_or_rule.asserted == True:
                    answer += " ASSERTED\n"
                    return answer
                else:
                    answer += "\n"
                    for support in fact_or_rule.supported_by:
                        answer += tab + "  SUPPORTED BY\n"
                        for supports in support:
                            answer += kb_explain_recursive(self, supports, indexer + 1)
                    return answer


        
        if isinstance(fact_or_rule, Rule):
            if fact_or_rule in self.rules:
                return kb_explain_recursive(self, self.rules.index(fact_or_rule),0)
            else:
                return "Rule is not in the KB"
        elif isinstance(fact_or_rule, Fact):
            if fact_or_rule in self.facts:
                return kb_explain_recursive(self, self.facts.index(fact_or_rule),0)
            else:
                return "Fact is not in the KB"
            
  
            
   def kb_retract(self, fact):
       """Retract a fact from the KB

       Args:
           fact (Fact) - Fact to be retracted

       Returns:
           None
       """
       printv("Retracting {!r}", 0, verbose, fact)
       ####################################################
       # Student code goes here
       #
       def rec_fun_fact(self, facter):
           factual = self._get_fact(facter)
           for x in factual.supports_facts:
               for dd in x.supported_by:
                   helper = dd[0][0]
                   if helper == factual:
                       x.supported_by.remove(dd)
                       if x.asserted == False:
                           if len(x.supported_by) == 0:
                               self.kb_retract(x)
           for y in factual.supports_rules:
               for qq in y.supported_by:
                   helper_a = qq[0][0]
                   if helper_a == factual:
                       y.supported_by.remove(qq)
                       if y.asserted == False:
                           if len(y.supported_by) == 0:
                               ruler = self._get_rule(y)
                               for potential_fact in ruler.supports_facts:
                                   for qq in potential_fact.supported_by:
                                       if qq[0][1] == ruler:
                                           potential_fact.supported_by.remove(qq)
                                       if len(potential_fact.supported_by) == 0:
                                           self.kb_retract(potential_fact)
                               self.rules.remove(ruler)
           self.facts.remove(factual)

       if not isinstance(fact,Fact):
           return
       else:
           working_fact = self._get_fact(fact)
           if working_fact == None:
               return
           if len(working_fact.supported_by) > 0:  
               working_fact.asserted = False
               return
           else:
               working_fact.asserted = False # check to see if this affects the fact in the kb
               n_a_content = [None, None]
               if working_fact.supports_facts == n_a_content:
                   working_fact.supports_facts = []
               rec_fun_fact(self, working_fact)



          
class InferenceEngine(object):
   def fc_infer(self, fact, rule, kb):
       """Forward-chaining to infer new facts and rules

       Args:
           fact (Fact) - A fact from the KnowledgeBase
           rule (Rule) - A rule from the KnowledgeBase
           kb (KnowledgeBase) - A KnowledgeBase

       Returns:
           Nothing           
       """
       printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
           [fact.statement, rule.lhs, rule.rhs])
       ####################################################
       # Student code goes here
       #we are going through all the rules comparing to one fact passed through, we are going to see if the new fact triggers any rules
       see_bindings = match(fact.statement,rule.lhs[0])
       if see_bindings != match(fact.statement,fact.statement):
           if see_bindings != False:
               if len(rule.lhs) > 1:  
                   list_helper = []
                   list_helper = rule.lhs
                   list_lhs = []
                   for x in rule.lhs:
                       if x != rule.lhs[0]:
                           new_statement = instantiate(x, see_bindings)
                           list_lhs.append(new_statement)
                   rhs_helper = instantiate(rule.rhs, see_bindings)
                   list_combinded = []
                   list_combinded.append(list_lhs)
                   list_combinded.append(rhs_helper)
                   inferred_rule = Rule(list_combinded)
                   pairs = [(fact,rule)]
                   inferred_rule.supported_by.append(pairs) #may need to look back at this
                   inferred_rule.asserted = False
                   kb.kb_add(inferred_rule)
                   fact.supports_rules.append(inferred_rule)
                   rule.supports_rules.append(inferred_rule)
                   
               else: 
                   new_statement = instantiate(rule.rhs,see_bindings)
                   new_fact = Fact(new_statement)
                   pairs = [(fact,rule)]
                   new_fact.supported_by.append(pairs) #may need to change
                   new_fact.asserted = False
                   kb.kb_add(new_fact)
                   fact.supports_facts.append(new_fact)
                   rule.supports_facts.append(new_fact)
                   
              
#just becasue you retract something, doesnt mean that you remove it, if it has supports, you dont remove it, you do set the assert to false though
#its alwyas being retracted, doesnt always have to be removed
#you do not retract rules, you remove a rule if there are no supports, you are only removing the rule if its part of the chain, have a seperate remove function that you call recusrively on the retract function

