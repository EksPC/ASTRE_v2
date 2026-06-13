package nl.tudelft.instrumentation.learning;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

public class WMethodEquivalenceChecker extends EquivalenceChecker {

    private final int w;
    private final AccessSequenceGenerator accessSequenceGenerator;
    private final DistinguishingSequenceGenerator distinguishingSequenceGenerator;

    public WMethodEquivalenceChecker(SystemUnderLearn sul, String[] inputSymbols, int w,
                                     DistinguishingSequenceGenerator dg,
                                     AccessSequenceGenerator ag) {
        super(sul, inputSymbols);
        this.w = Math.max(0, w);
        this.distinguishingSequenceGenerator = dg;
        this.accessSequenceGenerator = ag;
    }

    @Override
    public Optional<Word<String>> verify(MealyMachine hypothesis) {
        List<Word<String>> accessSequences = accessSequenceGenerator.getAccessSequences();
        List<Word<String>> middleSequences = generateMiddleSequences();
        List<Word<String>> distinguishingSequences = distinguishingSequenceGenerator.getDistinguishingSequences();

        if (distinguishingSequences.isEmpty()) {
            distinguishingSequences.add(new Word<>());
        }

        for (Word<String> access : accessSequences) {
            for (Word<String> middle : middleSequences) {
                for (Word<String> distinguishing : distinguishingSequences) {
                    Word<String> test = access.append(middle).append(distinguishing);
                    Optional<Word<String>> counterExample = findCounterExample(hypothesis, test);

                    if (counterExample.isPresent()) {
                        return counterExample;
                    }
                }
            }
        }

        return Optional.empty();
    }

    private List<Word<String>> generateMiddleSequences() {
        List<Word<String>> words = new ArrayList<>();
        generateMiddleSequences(new Word<>(), 0, words);
        return words;
    }

    private void generateMiddleSequences(Word<String> prefix, int depth, List<Word<String>> words) {
        words.add(prefix);

        if (depth == w) {
            return;
        }

        for (String symbol : inputSymbols) {
            generateMiddleSequences(prefix.append(symbol), depth + 1, words);
        }
    }

    private Optional<Word<String>> findCounterExample(MealyMachine hypothesis, Word<String> test) {
        String[] inputs = test.asList().toArray(new String[0]);
        String[] hypothesisOutput = hypothesis.getOutput(inputs);
        String[] sulOutput = sul.getOutput(inputs);

        int commonLength = Math.min(hypothesisOutput.length, sulOutput.length);

        for (int i = 0; i < commonLength; i++) {
            if (!hypothesisOutput[i].equals(sulOutput[i])) {
                return Optional.of(test);
            }
        }

        if (hypothesisOutput.length != sulOutput.length) {
            return Optional.of(test);
        }

        return Optional.empty();
    }
}