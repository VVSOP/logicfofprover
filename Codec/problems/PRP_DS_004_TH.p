fof(heads_i_win,axiom,   (heads => i_win)).
fof(tails_you_lose,axiom,(tails => you_lose)).
fof(heads_or_tails_exclusive,axiom,(tails <~> heads)).
fof(i_win_then_you_lose,axiom,(i_win <=> you_lose)).
fof(i_win,conjecture,i_win).
