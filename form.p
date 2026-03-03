tff(species_decl,type,
    species: $tType ).

tff(eats_decl,type,
    eats: ( species * species ) > $o ).

% {eater} eats {eaten}

tff(link_decl,type,
    link: $tType ).

tff(eater_lnk_decl,type,
    eater_lnk: link > species ).

tff(eaten_lnk_decl,type,
    eaten_lnk: link > species ).

tff(primary_decl,type,
    is_primary: species > $o ).

tff(apex_decl,type,
    is_apex: species > $o ).

tff(depeneds_decl,type,
    depends: ( species * species ) > $o ).

tff(chain_decl,type,
    chain: $tType ).

tff(start_decl,type,
    start_of: chain > species ).

tff(end_of_decl,type,
    end_of: chain > species ).

tff(complete_decl,type,
    is_complete: chain > $o ).

% Axiom: The eater of a food link eats the eaten of the link.

tff(ax_eaten,axiom,
    ! [E: link] : eats(eater_lnk(E),eaten_lnk(E)) ).

% Axiom: No cannibalism

tff(foodlink_eater,axiom,
    ! [E: link] : ( eater_lnk(E) != eaten_lnk(E) ) ).

% Axiom: Every species eats something or is eaten by something (or both).

tff(no_lone_species,axiom,
    ! [A: species] :
    ? [B: species] :
      ( eats(A,B)
      | eats(B,A) ) ).

% Axiom: Someting is a primary producer iff it eats no other species

tff(is_primary,axiom,
    ! [A: species] :
      ( is_primary(A)
    <=> ~ ? [B: species] : eats(A,B) ) ).

% Theorem: If something is a primary producer then there is no food link such that the primary producer is the eater of the food link.

tff(primary_not_hungry,conjecture,
    ! [A: species] :
      ( is_primary(A)
     => ~ ? [E: link] : ( eater_lnk(E) = A ) ) ).

% Theorem: Every primary producer is eaten by some other species

tff(all_primary_feed,conjecture,
    ! [A: species] :
      ( is_primary(A)
     => ? [B: species] : eats(B,A) ) ).

% Theorem: If a species is not a primary producer then there is another species that it eats.

tff(primary,conjecture,
    ! [A: species] :
      ( ~ is_primary(A)
     => ? [B: species] : eats(A,B) ) ).

% Axiom: Something is an apex predator iff there is no species that eats it.

tff(is_apex,axiom,
    ! [A: species] :
      ( is_apex(A)
    <=> ~ ? [B: species] : eats(B,A) ) ).

% Theorem: If something is an apex predator then there is no food link such that the apex predator is the eaten of the food link.

tff(apex_no_fl,conjecture,
    ! [A: species] :
      ( is_apex(A)
     => ~ ? [E: link] : ( A = eaten_lnk(E) ) ) ).

% Theorem: Every apex predator eats some other species.

tff(apx_eats,conjecture,
    ! [A: species] :
      ( is_apex(A)
     => ? [B: species] : eats(A,B) ) ).

% Theorem: If a species is not a apex predator then there is another species that eats it.

tff(no_apex_eaten,conjecture,
    ! [A: species] :
      ( ~ is_apex(A)
     => ? [B: species] : eats(B,A) ) ).

% Axiom: For every food chain, the start of the chain is the eaten of some food link, and one of the following holds: (i) the eater of the food link is the end of the food chain, xor (ii) there is a shorter food chain (shorter by one food link) from the eater of the food link to the end of the whole food chain.

tff(no_apex_eatenyyyyy,axiom,
    ! [C: chain] :
    ? [L: link] :
      ( ( start_of(C) = eaten_lnk(L) )
      & ( ( end_of(C) = eater_lnk(L) )
      <~> ? [G: chain] :
            ( ( start_of(G) = eater_lnk(L) )
            & ( end_of(G) = end_of(C) ) ) ) ) ).

% Axiom: There is no food chain from a species back to itself (no death spirals).

tff(no_death,axiom,
    ! [S: species] :
      ~ ? [C: chain] :
          ( ( start_of(C) = S )
          & ( end_of(C) = S ) ) ).

% Axiom: A complete food chain starts at a primary producer, and ends at an apex predator.

tff(complete_chains,axiom,
    ! [C: chain] :
      ( is_complete(C)
    <=> ( is_primary(start_of(C))
        & is_apex(end_of(C)) ) ) ).

% Axiom: Every species is in some complete food chain, i.e., (i) the species is the primary producer start of the complete food chain, or (ii) the species is the apex predator at the end of the complete food chain, or (iii) there is a non-complete food chain from the start of the complete food chain to the species, and another non-complete food chain from the species to the end of the complete food chain.

tff(complete_chains_okay,axiom,
    ! [A: species] :
    ? [C: chain] :
      ( ( is_complete(C)
        & ( start_of(C) = A )
        & is_primary(A) )
      | ( is_complete(C)
        & ( end_of(C) = A )
        & is_apex(A) )
      | ( is_complete(C)
        & ? [G: chain,K: chain] :
            ( ( start_of(G) = start_of(C) )
            & ( end_of(G) = A )
            & ( start_of(K) = A )
            & ( end_of(K) = end_of(C) )
            & ~ is_complete(G)
            & ~ is_complete(K) ) ) ) ).

% Theorem: The start species of a complete food chain does not eat the end species.

tff(start_specs,conjecture,
    ! [C: chain] :
      ( is_complete(C)
     => ~ eats(start_of(C),end_of(C)) ) ).

% Theorem: If a species is neither a primary producer nor an apex predator, then there is a food chain from a primary producer to that species, and another food chain from that species to an apex predator.

tff(specs_okayyyy,conjecture,
    ! [A: species] :
      ( ( ~ is_primary(A)
        & ~ is_apex(A) )
     => ? [C: chain,G: chain] :
          ( is_primary(start_of(C))
          & ( end_of(C) = A )
          & ( start_of(G) = A )
          & is_apex(end_of(G)) ) ) ).

% Axiom: Given two species, the first depends on the second iff there is a food chain from the second to the first.

tff(depends_okiii,axiom,
    ! [A: species,B: species] :
      ( depends(B,A)
    <=> ? [C: chain] :
          ( ( start_of(C) = A )
          & ( end_of(C) = B ) ) ) ).

% Theorem: If a species is not an apex predator then there is an apex predator that depends on the species.

tff(specs_apex_okayyyi,conjecture,
    ! [A: species] :
      ( ~ is_apex(A)
     => ? [B: species] :
          ( depends(B,A)
          & is_apex(B) ) ) ).

% Theorem: An apex predator depends on all primary producers of all complete food chains that end at the apex predator.

tff(spered_apex_okayyyi,conjecture,
    ! [A: species,B: species] :
      ( ( is_apex(A)
        & is_primary(B) )
     => ( ? [C: chain] :
            ( is_complete(C)
            & is_apex(end_of(C))
            & is_primary(start_of(C)) )
       => depends(A,B) ) ) ).