package de.wiesler;

public final class Increment {
    public final boolean occupied;
    public final int position;

    /*@ public normal_behaviour
      @ requires true;
      @ ensures this.occupied == occupied;
      @ ensures this.position == position;
      @ assignable \nothing;
      @*/
    public Increment(boolean occupied, int position) {
        this.occupied = occupied;
        this.position = position;
    }
}
