package infra;

import java.time.Duration;
import java.time.Period;

public class Delta {

    private Period min;
    private Period max;
    private Duration granularity;

    public Delta(Period min, Period max, Duration granularity)
    {
        this.min=min;
        this.max=max;
    }

    public Period getMax() {
        return max;
    }

    public Period getMin() {
        return min;
    }

    public Duration getGranularity() {
        return granularity;
    }
}
