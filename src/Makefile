######################################################
#                                                    #
#                    ,MMM8&&&.                       #
#                _..MMMMM88&&&&..._                  #
#            .::'''MMMMM88&&&&&&'''::.               #
#           ::     MMMMM88&&&&&&     ::              #
#           '::....MMMMM88&&&&&&....::'              #
#              `''''MMMMM88&&&&''''`                 #
#                    'MMM8&&&'                       #
#                                                    #
#                     SATurne                        #
#                ----------------                    #
#             A tiny verified solver                 #
#                                                    #
######################################################
VS = $(wildcard *.v)
VOS = $(VS:.v=.vo)

.PHONY: all clean mr-proper
all: ${VOS}

%.vo: %.v
	@ echo "Compiling $<"
	@ coqc -R ./ Src $< -o $@

clean:
	@ rm -f ${VOS}

mr-proper: clean
	@ rm -f .*.aux *.glob

