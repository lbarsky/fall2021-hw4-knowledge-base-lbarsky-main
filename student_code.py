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

    def fact_rule_retract(self, fact_rule):
        if fact_rule in self.facts:
            #print("Index of fact in the list is ", self.facts.index(fact))
            #fact_from_list = self.facts[self.facts.index(fact_rule)]
            if len(fact_rule.supported_by) != 0:
                return
            else:
                self.facts.remove(fact_rule)
                for fr in fact_rule.supports_facts: #1 remove this fact from fr.supported_by and 2 call retract on fr
                    fr.supported_by.remove(fact_rule)
                    fact_rule_retract(self, fr)
                for fr in fact_rule.supports_rules:
                    fr.supported_by.remove(fact_rule)
                    fact_rule_retract(self, fr)
        if isinstance(fact_rule, Rule) and not fact_rule.asserted:
            if len(fact_rule.supported_by) == 0:
                self.rules.remove(fact_rule)
            else:
                return
                #only do something if rule is unasserted and unsupported?

    def kb_retract(self, fact):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        fact_rule_retract(self, fact)
        printv("Retracting {!r}", 0, verbose, [fact])
        ####################################################
        # Student code goes here


            #See if the fact is supported; don't retract if it is
            #print("The fact is supported by ", fact_from_list.supported_by)
            #If the fact is supported, just return
            #If the fact is unsupported, go through other rules & facts that are supported by this one
            # If those facts/rules become unsupported, and are *not* asserted (asserted=False), then remove them

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
        ####################################################
        # Use the `util.match` function to do unification and create possible bindings.
        for rule1 in rule.lhs:
            bindings = match(fact.statement, rule1)

            if bindings:
                # Use the `util.instantiate` function to bind a variable in the rest of a rule.
                print("New Binding! ", bindings)
                if len(rule.lhs) > 1:
                # If the rule has 2 or more elements on the LHS, make a new rule w/bindings
                    lhs_bindings = [instantiate(lhs_item, bindings) for lhs_item in rule.lhs[1:]]
                    rhs_binding = instantiate(rule.rhs, bindings)
                    new_rule = Rule([lhs_bindings, rhs_binding], supported_by=[[fact, rule]])
                    new_rule.name = "inferred " + str(new_rule)
                    print(" *** New rule:", new_rule)
                    kb.kb_add(new_rule)
                    rule.supports_rules.append(new_rule)
                    fact.supports_rules.append(new_rule)
                else:
                # The rule only has one element on the LHS
                # check to make sure the RHS of the rule is bound
                    rhs_binding = instantiate(rule.rhs, bindings)
                # if all terms are now Constants, state the RHS as a fact
                # terms = fact.statement.terms + rhs_binding.terms
                # for t in terms:
                #    if is_var(t):
                #        return
                    new_fact = Fact(rhs_binding, supported_by=[[fact, rule]])
                    new_fact.name = "inferred fact " + str(new_fact.statement)
                    print(" *** New fact:", new_fact)
                    kb.kb_add(new_fact)
                    rule.supports_facts.append(new_fact)
                    fact.supports_facts.append(new_fact)