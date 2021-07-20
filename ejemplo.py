from belief_revision_engine import cnf, belief_base,entails,expand,contract,revise

b = belief_base()
for beliefs in ['p','q^r']:
    expand(b, beliefs)
print("b is: {}".format(b))
revise(b, 'p^q')
print("Despues de la revision, b is: {}".format(b))
print("implica p? {}".format(entails(b,'p')))
expand(b, '~p^q')
contract(b,'p','full-meet')
print("despues de la contraccion, b is: {}".format(b))
print("implica p? {}".format(entails(b,'p')))
