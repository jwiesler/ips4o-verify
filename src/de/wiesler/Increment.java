package de.wiesler;

public final class Increment {
    public final boolean occupied;
    public final int position;

    /*@ public normal_behaviour
      @ requires_free true;
      @ ensures_free this.occupied == occupied;
      @ ensures_free this.position == position;
      @ assignable_free \nothing;
      @*/
    public Increment(boolean occupied, int position) {
        this.occupied = occupied;
        this.position = position;
    }
}
