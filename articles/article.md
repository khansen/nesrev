# Reverse Engineering NES Games With Hard Discipline

_Last updated: 2026-09-21_

This article describes a repeatable process for reverse engineering
NES games. The process has proven highly effective with LLM (Large Language Model) support. The core
principles and techniques are applicable for any platform where suitable
tooling (e.g., a disassembler, an assembler, and an emulator) exists, not just NES programs.

Why would you want to do this? For learning how your favorite
classic games work, and for fun! You might even discover _new_ (as in _very old_) bugs in the code, or learn why some known bugs occur (and how they could be fixed). For speed running, you could figure out exactly how a game's timing, pseudo-randomness, collision handling and so on work. You can create Game Genie codes for all sorts of targeted effects.

I've previously partially reverse engineered a handful of NES games in an _ad hoc_ fashion. I didn't follow a particular plan or process, just trial and error. I used a combination of tools, including disassemblers, hex editors, tile editors, emulators, _corrupters_, and text editors. That style can be fun and is a great way of learning. The results can be wholly sufficient if your goal is to write a level editor or password generator, for example. However, if your goal is to reverse engineer a game completely, down to documenting the last byte, you'll want to apply some rigor to the process.

## From mechanical disassembly to semantic source code

The canonical inputs to the reverse engineering process are a) the game's binary ROM image, and
b) player-facing documentation, such as the instruction manual and strategy
guides. The outputs are a) a legible representation of the code and
data, and b) supporting technical documentation. The results may (for all we know)
exceed the level of quality of the original source code, if we did a
thorough enough job with it.

When the reverse engineered project assets are built (assembled) anew, the output should
be a ROM image whose contents are identical to the original. We haven't
changed anything about the game itself, only "alchemized"
its code so that it can more easily be understood and worked with.

Here's an example of a "wall of hex" code (6502 assembly language) before we ran the process:
```
    JSR LC81A
    JSR LC947
    JSR LC911
    JSR LCA1F
    JSR LC468
    JSR LC941
    JSR LD29E
    JSR LD1BA
    JSR LD2C6
    JSR LD705
    JSR LD83C
    JSR LDA32
    JSR LD583
    JSR LE386
    JSR LE9C4
    JSR LEBC7
    JSR LEF79
    JSR LF061
    JSR LF492
    JSR LF5AF
    JSR LF845
```

Here's what the same block of code can look like at the end of the process:
```
    JSR UpdateSealTopiEntrants
    JSR UpdateCondorAI
    JSR UpdatePlayerInteractionFlags
    JSR ProcessActorPlayerInteraction
    JSR UpdateSealTopiAI
    JSR UpdateEnemyAI
    JSR UpdatePlayerTimers
    JSR UpdateCloudMotion
    JSR CheckPlayerBonusItemCollisions
    JSR UpdatePlayerSyncMotion
    JSR CheckPlayerEnemyCollisions
    JSR UpdatePlayerSpawnState
    JSR UpdatePlayerFlashState
    JSR UpdatePolarBearAI
    JSR CheckPlayerMountainPeakInteraction
    JSR UpdateBonusVegetables
    JSR CheckPlayerCloudInteraction
    JSR UpdateHammerStrikeEffect
    JSR ProcessEnemyActorDeath
    JSR DispatchActorSpriteRendering
    JSR UpdatePlayerOamState
```
Now it's possible to understand what those subroutines (functions) are about! From there, you can deep-dive into the code and documentation yourself, or you can ask an LLM all sorts of questions about the code and data, such as "what determines when the polar bear appears?", "how are levels stored?", "how do the bonus stages work?", and "how can I get a life?".

## Philosophy

Imagine that you're a developer who inherits a mature software project (an NES game!). You've dreamt of this opportunity since you were a kid.
You are already comfortable with the target platform (hardware, programming language,
and tools), but you've never seen the implementation of _this_ particular
game. The original developers are no longer around to answer thoughtful questions, or their memory conspicuously got really hazy ever since they were reassigned to projects targeting the latest newfangled system (_Super Nintendo?! Blech!_), and they don't get extra points for helping you anyway. Because of a surge in interest for classic games, you
get tasked with making a few improvements to the program (a "Deluxe", or "DX", version) for the game's re-launch.
As always, the deadline is tight. If you are to have any hope of accomplishing this feat, the source code and accompanying documentation
must facilitate _onboarding_ of new developers. The code must be readable,
maintainable, and extensible. Algorithms and data formats must be documented. My goal
is that the projects (re-)created through the reverse engineering process have these qualities. As a developer,
you shouldn't notice that they are a product of reverse engineering. You should be thinking: "Wow, that's some fine looking code and documentation that I'm humbled to work with; I solemnly swear to follow its high standards in my own patchwork".

## Reproducibility and beyond

Once the source code is perfectly legible, we shouldn't be afraid to break
free from the shackles of _binary parity_ and make modifications (_mods_) to
the game. Mods can range from configuration tweaks (e.g., number of lives) to
bug fixes to optimizations to changing level designs to composing new music to implementing new
behaviors and features. Anything is possible. As we will see, mods can also be used to support runtime analyses of the game, whose results can be used to further improve the quality of the project (static code and documentation).

## Legal disclaimer (but I'm not a lawyer)

I'm not publishing the complete, verbatim _output_ of the reverse engineering work.
I'm only publishing the tools, scripts, and documentation needed to _run_ the
process. If you want to run it, you will need to obtain a suitable ROM image (e.g., by dumping the ROM from a physical game cartridge you own)
and game reference documentation (e.g., a PDF you made from scanning your physical copy of the manual). Last I checked, Nintendo's Japanese website offered PDF versions of several NES manuals as free downloads. The process scripts will not download any external game assets.

Creating mods is a great way to play and learn, but you should be careful
about distributing the resulting code or ROM in full, since the work is derivative.
If you want to share your mod with others, sharing the patch file that is created by the mod script is a safer option. A patch file contains only the delta (changed bytes)
relative to the original ROM, so that someone else who is in legal possession of the
original ROM can materialize your modded ROM by applying the patch.

## Reversing in the small and large

If you're a newbie rock climber, you don't _free-solo_ El Capitan on your first trip. Likewise, reverse engineering "Kirby's Adventure" as your first project could be tough if you're going at it alone. I started by targeting first generation NES ("black box") games with only 16 kilobytes
of program ROM. These projects rarely exceed ten thousand lines of code, yet they have ample complexity. They establish foundational organization, techniques, library-like code, and data formats that are also commonly found in larger projects. Using a
decent LLM (a frontier model in 2026), most 16 KB projects can reach a mature status in a day or two. These projects are great
for building out an effective baseline harness for reverse engineering. The bigger the game, the bigger (and costlier) the consequences of a poor process. For small games, we can comparatively cheaply run the whole process from scratch after making process improvements, compare the results, and make further adjustments. Similarly, we can run the whole process with the same game but different LLMs and compare. This increases our confidence in the robustness of the process itself, as opposed to being at the mercy of the whims of a particular model.

The jump from 16 KB to 32 KB ROMs is conceptually not substantial, and it's not necessarily double the work per project. The whole ROM still fits snugly in the NES's addressable memory. Larger ROM sizes add another dimension in the form of bank-switching, but it can be handled with a few extensions to the core process. At the time of writing, the process is stable enough that an MMC1 game like Metroid (128 KB) can be handled comfortably.

## Static vs dynamic analysis

Usually, the bulk of the work is static analysis of a game's code and data. In my experience, the results can be extremely good without the LLM having to rely on abundant runtime studies. This could be due to the models' clever use of _triangulation_ from static analysis and the game manual alone, or it could be that the models I've used have already been trained on existing (community) disassemblies of some of these games. All results still need to be reviewed for semantic correctness and completeness, but it's been rare that something was _completely_ off base.

There will be cases in each project where dynamic analysis is needed to raise confidence or fill the gaps. Dynamic analysis involves preparing instrumentation, running the game in an emulator, interacting with it, observing it, and processing and interpreting the trace logs. The findings should then be fed back into the source code and documentation, which can trigger new insights. For example, static analysis might not be able to prove with 100% certainty the semantic names for "Enemy type 1" (turtle?) and "Enemy type 2" (crab?), or "Sound effect 1" (kick?) and "Sound effect 2" (punch?), although it could offer some guesses/hypotheses (e.g., based on already inferred semantics of surrounding code or data).

Dynamic analysis can help eliminate most unknowns in the code, but doesn't (yet) lend itself quite as well to automation in all cases. As models become more capable and can in many cases play the game in an emulator fully unattended, and even "see" the graphics and "hear" the audio, this ratio can change (and rather become a function of the needs of each project). With a scriptable, introspectable emulator like FCEUX, a capable model can run its own experiments with the same ease as it can do static analysis.

## Harness

The process is supported by a set of shell scripts, which wrap various tools. The scripts are invoked by running `make` commands. An LLM can learn about these commands by reading the `AGENTS.md` file and the associated _playbooks_ in the repository. The process should enable an operator (LLM or human) to make informed choices that consistently and reliably produce plausible results, i.e. _leave the project in a better state than when you started_. The scripts make sure that the rules of change management are followed at every step, and that attempts at straying from the path are met with resistance.

Again, the scripts are just there for support and streamlining; the real analysis work and decision-making is done by the operator, outside the scripts. The scripts provide current status, can suggest items to work on, and they yell if the operator isn't doing something _by the book_. However, the scripts cannot catch the operator's mistakes that are the most severe: _Assigning wrong names to symbols_.

The tooling also wants to ensure that all projects follow the same standards and are inter-consistent. There's no reason to use different naming conventions, formatting rules, and idioms in each project. As more projects are completed, operators can find many exhibits of  sanctioned code. New projects should apply a standard treatment when familiar-looking code and data formats are detected. As the process and standards are gradually improved, older projects should be updated so that they also benefit from the improvements and so that they can always be worked on with the latest version of the tooling.

The _playbooks_ lay out all the rules for how the process should be run, the source code style, how to use the tools, how to write documentation (and _what_ to document), how to review changes, how to assess when a project is _Done_, and so on.

The process is supposed to stop the operator from repeating "boring" mistakes I've encountered when reviewing real changes. The code should look tasteful ("Kent's style") at first sight; I shouldn't have to request ad hoc changes that concern mechanics or aesthetics. If the review can be focused entirely on semantics, then the process works as intended. This has been and still is an iterative process of refinement: Interrogate the model about poor decisions it made or wretched code it produced, codify the standards by updating scripts and/or playbooks, re-do the reverse engineering work in a fresh session, and scrutinize the new results.

Occasionally, we might find a good reason to extend the process in a material way, such as requiring the operator to produce a _ledger_ (CSV file) that documents a dimension of the project work. Obviously, projects that were already completed will lack those artefacts, and updating (_backfilling_) them could be non-trivial (e.g., requires extensive re-analysis of code and data). A non-intrusive way of adding a new feature to the process is to make the feature _opt-in_ at first: It should be _on_ by default for new projects, but not required for existing projects. This can be achieved by adding a feature flag to the project configuration (`project.conf` file) and checking for the presence of that flag in the relevant scripts. This way, the feature can be added to projects one by one. Once all projects have been updated, the feature flag can be removed.

## The Reverse Engineering Loop

The core activity in reverse engineering is to perform
semantic analysis of some part of the project's assets (code and data), and use
the findings to make some (bounded) changes to the project that make it easier to
understand, maintain, and extend. The changes should ideally be subjected to peer review (human or LLM). Once this ritual has been performed enough times, the project should eventually reach some "Definition of done", or _gold standard_. How many iterations it will take to reach this point, and the quality and "correctness" of the final results, depends on many factors: The size and complexity of the game, the quality and completeness of the reference documentation, the quality of the tooling (disassembler, assembler, emulator), the quality of the process support (playbooks and scripts), and the performance of the operator(s) (adherence to the process; analytical abilities; planning and judgment; mid-process review and feedback).

The changes that can be made to a project roughly fall into the following
categories:
- Renaming a code label so that it better conveys what the code does.
- Renaming a data label so that it better conveys what the data are and are used for.
- _Localizing_ a label so that it stays private to a subroutine.
- Formatting a piece of data so it's easier to read and change.
- Replacing an embedded pointer (in data or in code) with a symbolic reference, introducing a new label at the target address if needed.
- Replacing a raw data address (an instruction operand) with a symbolic reference.
- Replacing a literal value ("magic number") with a semantic alias.
- Formatting a literal value so it's more "human-readable" (e.g., decimal instead of hex).
- Replacing a hardcoded length or offset with an expression involving labels.
- Documenting a subroutine via source comments.
- Documenting a piece of data via source comments.
- Documenting a subsystem or algorithm.
- Documenting a data format.

In addition, there are meta-activities associated with the above:
- Documenting the scope/target of the next pursuit and why it was selected.
- Documenting the actual changes that were done (e.g., "renamed LC000 to ResetHandler with high confidence", "symbolized address $0048 as ZP_Player1Lives with medium confidence").
- Documenting an uncertain/placeholder name that should be revisited later.
- Documenting that the role and format of a particular data blob were (supposedly) proven.
- Documenting findings that weren't acted upon right now, but that may inform further work ("scratchpad").
- Recording progress towards mechanical goals (described below).
- Recording friction in the process itself (tooling, scripts, and documentation).

This process happens to be a very good fit for an _agentic loop_.

## "A pass" as unit of work

At each "loop iteration" (or _pass_ over the project), the operator should pick something that seems timely to do, transform some assets (source code or documentation), and document what was done (in one or more meta-data files).
Each pass should produce a tangible result by expending a reasonable effort.
The scope per pass should not be too small and not too large. If it's too small, many passes will be needed to make substantial progress, and a lot of
program analysis will likely have to be repeated (because the same sections are visited
many times). Names can have lower confidence and quality because there is less context to
work with. An example of poor scoping is to always rename a single LXXXX label per pass, or to symbolize a single raw RAM address per pass.

If the scope is too big, both the length (cost) of the session and the results can become
unpredictable and/or unmanageable. Reviewing large changes is more taxing. _Reviews_
(performed by humans or LLMs) are important for making sure that newly introduced names seem reasonable and coherent, and for verifying that the process is being followed (beyond what the scripts can catch).

Minimizing the number of passes (or tokens) for reaching "Definition of done" is not a goal in itself. If spending a few more passes can materially improve the project's quality, that one-time effort will pay off repeatedly, each time someone wants to study the project or further improve it.

For all the rigorous playbooks and scripts in the world, picking an appropriate pass scope remains somewhat of an art, but it does get easier with experience. If forced to choose, I would rather err on the side of too big than too small scope, because micro-passes are a symptom of a process that isn't working well. Micro-passes can be used as a form of procrastination when the operator is hesitant to make a decision that _must_ be made before the project can move forward materially. When faced with the risk of introducing a poor semantic name, the operator might curl up and stay in the "safe zone" of inconsequential edits.

The pipe dream is that the harness is robust enough that the prompt "Do the next pass" is all it takes to bring the project one step closer to completion, with minimal steering (babysitting) needed.
To this end, how much freedom should the operator get in deciding
what, and how much, to do in each pass? At one end of the scale, we can simply tell the LLM to "work on this project" without enforcing any methodology; that's what I experimented with first (because it was alluring; just let the model figure out what to do and how to do it, no guardrails!). At the other extreme, we could enforce a very rigid pass strategy where the operator is
severely constrained: First, rename LXXXX labels (in some arbitrary (mechanical) order, e.g. ranked by "most used"), then
symbolize RAM addresses (again in some arbitrary order), then symbolize and format literal values, then ... That's what I tried after experiencing that the "unhinged" approach (with a frontier model in the spring of 2026) gave unpredictable results.

The middle ground is to give the operator sufficient autonomy to adapt the pass based on the maturity of the project. Here's a reasonable strategy:
- Early in the process, trace the reset and NMI (Non-Maskable Interrupt) handlers. This should be sufficient to locate a few key subsystems in the game (title screen, audio driver, ...).
- Then, drill down into subsystems and stay within a "corridor" of the code for however many passes it takes, doing as much semantic work (along multiple axes -- renaming/symbolizing, analyzing data, formatting, documenting) as is reasonable.
- Once in a while, assert coherency beyond individual passes and corridors.
- Along the way, the process scripts should surface any signals that indicate the operator isn't fulfilling their duties (in case they are missed in peer reviews).
- In later passes, use runtime analysis to eliminate uncertainty.
- In even later passes, see the big picture of all the subsystems working together (inter-coherency).
- In even later passes, polish smaller areas until there are no (known) unknowns left.
- Once all semantics have (supposedly) been figured out, write high-level systems documentation.

Working on coherent chunks of code per pass during the middle phase is key to covering more ground effectively. When renaming a subroutine, the operator should try to symbolize the RAM addresses accessed by the subroutine too, and document the subroutine's input/output contract through code comments (when it isn't obvious). When naming a data table used by a subroutine, the operator should analyze the access patterns and try to figure out the shape of the data, and then reformat, comment, and document the data (format and extents) at the same time.

The operator needs to balance the scoping of passes against the goal of minimizing _churn_. Writing "stable" documentation too early, before a system is figured out, means that the documentation will have to be revised later. Referring to low-confidence symbol names in code comments means that the comments will have to be updated if those symbols are renamed later. Not capturing the formats and extents of data blobs means that those blobs must be revisited later.

## Working notes

The operator should maintain a `WORKING_NOTES.md` file per project. Working notes are a durable memory of discoveries that were made during a pass, that couldn't be fully utilized as part of the pass itself, and that cannot be captured in one of the structured ledgers (CSV files). Working notes must be forward-facing: If the information isn't relevant for some future pass, it doesn't qualify. Working notes should be acted on at some point, not accumulated forever. If the operator _never_ writes any working notes, that can be an indication of a process issue (e.g., passes aren't scoped appropriately, or genuinely useful discoveries aren't captured).

The main reason I introduced `WORKING_NOTES.md` as a mandatory part of the process was frustration due to LLM _context compaction_; forcing the operator to write down their discoveries in a timely manner reduces the impact of memory loss inflicted at the most inconvenient times.

## Peer review

The process mandates that the operator (implementer) performs a _self-review_ of the changes before declaring the pass finished. Even better results can be achieved by performing peer reviews in addition. The review can be performed by a human, but it's also possible to fully automate reviews. This can be done by having the implementer create a _review packet_ Markdown file per pass, and tell the other operator (the reviewer LLM, running in `tmux`) to review the pass. The two operators can then communicate by watching and writing files. The whole review transcript is added to git, and thus becomes part of the pass's documentation. This setup is supported by the `agent_review_tmux.py` script. By default, Codex is the implementer and Claude is the reviewer.

## Surfacing process friction

Operators (implementers and reviewers) should always be on the lookout for potential issues with the process itself, and record them in `PROCESS_FRICTION.md`. Examples of friction are when scripts produce wrong results or have undesired side-effects, or when gaps in the playbooks cause low-quality reviews.

The raw recordings in `PROCESS_FRICTION.md` become opportunities for learning and improvement. Findings should be triaged and acted upon regularly, so that the process is improved where it's most likely to benefit the next passes. (This "process of process improvement" can largely be automated, too.)

## Technical documentation

In addition to semantic source code, the process should produce supporting technical documentation. The documentation should complement the code, not regurgitate implementation details in prose. A developer should be able to consult the documentation to find how core aspects of the game work. High-level systems documentation should be collected in a `DX_Systems.md` file. Subsystems and data formats can be documented in separate files, as needed.

While the exact nature and scope of the documentation will vary per project, several of the following categories are typically relevant:
- If the game uses _passwords_, the password system and data format should be documented.
- If the game has a _map system_, the map data format(s) should be documented.
- If the game has _levels_ with different designs, the level data format(s) should be documented.
- If the game has an _object system_ (player objects, enemies, etc.), object layouts and data formats should be documented. Rendering, physics, and collision detection should be documented.
- If the game has an _attract/demo mode_, the format of simulated inputs should be documented.
- Audio (music and sound effects) formats should be documented.
- The overall program structure (main loop and core service routines) should be documented.

For a (supposedly) mature project, it's a red flag if the technical documentation doesn't cover aspects that you know are relevant for the particular game. The operator is required to populate a `data_format_targets.csv` file that documents which common documentation categories are covered and which are not applicable.

The process should produce a `CURIOSITIES.md` file. A _curiosity_ is something genuinely odd, interesting, or buggy about the ROM. The curiosities file is arguably "just" a bonus of completing the process, but curating it is my favorite part of every project; once code and data are semantic through and through, they become a gold mine for finding and explaining technically interesting aspects, both user-visible (bugs) and invisible.

## Mechanical quality gates

Several properties of a project can be measured mechanically in an effort to
assess the project's status and maturity. These include:

- Binary parity. This gate must be green at every stage (i.e., after every transformation);
  the produced ROM is never allowed to drift from the reference (source of truth).
- Number of LXXXX labels (code and data). The goal is always zero.
- Number of raw data address references. The goal is always zero.
- Number of raw literals (instruction operands -- candidates for "magic numbers"). The goal is _not_ zero (as that would be pathological).
- Number of undocumented subroutines / global code labels.
- Number of undocumented data labels.
- Number of _unacknowledged_ data blobs. The goal is always zero.
- Whether all relevant subsystems and data formats have been documented.

For an unfinished project, the metrics can give a _rough_ indication of the amount of work
that remains. Obviously, except for binary parity, it's very easy to _game_ these metrics (reward hacking!).
Instead of spending considerable effort on deducing high-confidence, semantic label names,
I could just name them `Frobnicate1` through `FrobnicateN`. Similarly, I could add a generic placeholder "documentation comment" to all subroutines and data labels. Finally, I could introduce an unhelpful alias `MAGIC_FF` for the constant `$FF`. Such shameful acts don't contribute value and only create a false impression
of the project's maturity. They should never pass peer review. Imagine how upset a fellow developer would be if they came into a "finished" project expecting to be enlightened, only to find that it's a smokescreen.

Just because binary parity is preserved does not mean that a symbolization of a code address, RAM address or a literal value was semantically correct. The mechanical gates can't assess this. A classic example is when a broad search-and-replace of a literal doesn't account for the fact that the same value can have different meanings in different contexts. An incorrect, misleading symbolic name is worse than a non-semantic, raw value. The same care is needed when symbolizing raw RAM addresses; it is quite common that a single physical RAM address serves different purposes in different parts of the program, so that usages must be symbolized accordingly (carefully and conservatively). (This technique is called _overlaying_ and is popular in resource-constrained systems.)

## Measuring real quality

Objectively measuring the quality of a project, and saying whether it is "Done", is hard. Even with the best of intentions, an operator's choice of a symbol name can be plain wrong. Often, a symbol will be
_inferred_, with some level of certainty, ranging from high to low. A symbol might prematurely (erroneously) be classified as having "high certainty"; if that assertion isn't challenged in review, it could still be wrong but the name will never be revisited. How can we be sure that
the chosen name is at best "correct" (what an oracle would say), at least "justified" (based on available evidence), and certainly not misleading? Only by deeply understanding
the code, perhaps corroborated by runtime observations. It can be a bit like working
on a hard sudoku puzzle; you might place a "probe" to check if a solution works out. Some steps later, the probe can be proven wrong, and you have to
backtrack. Similarly, in reverse engineering, if a symbol is named wrong, other symbols
could be named wrongly based on it, before the mistake is (hopefully) discovered. But
unlike suduko, there is no unambiguous (mechanical) signal that says "this piece is 100% wrong".
However, as more and more symbols are inferred and become part of a bigger
picture, the analysis and reviews will hopefully detect any contradictions. If a mistake is found, the pass history (_provenance_) helps to unwind the renamings (and maybe understand how things went wrong, in case the process can be improved). Operators and reviewers should avoid the sunk cost fallacy and instead be prepared to challenge previous decisions at any time.

Assuming that symbols are named correctly and consistently, there are some objective, universally agreed traits of
quality code we can check for in reviews:
- Code comments complement the actual code, instead of  redundantly echoing it.
- Magic numbers are symbolized and documented.
- Constants are human-readable (e.g., decimal instead of hex), where applicable.
- Offsets and sizes are computed from labels
instead of hardcoded.
- Tables and other data structures are formatted and documented in a way that makes them easy to read and modify.

Just because the code has been reverse engineered from a non-semantic disassembly does not mean it gets a free pass to skimp on any of these criteria.

Ultimately, the only way to find out if the code and documentation pass muster is to _use_ them concretely. Pick some topic you want to study, for example how bonuses and extra lives work. Are you able to find the relevant code? Are you able to understand it? Are you able to tweak it (in a mod)? Are the aspects covered in the documentation? In several cases, when I sought out specific information in a project ("how do doors work in Kid Icarus?"), I found gaps in both semantics, data formatting, and documentation.

## Relocation test

The holy grail of a reverse engineering project is to be able to change the size and location
of symbols (code or data) without breaking the program, i.e. having everything _relocatable_.
This opens the door to making arbitrary changes to the game's code and assets -- not just _overwriting_ a byte value here and there (which you could already do with a Game Genie code).

A simple test
for checking if symbols _seem_ relocatable is to insert a dummy byte at the beginning of the
program; this will shift all symbols' addresses by +1 byte:

```
.ORG $C000

.DB 0 ; inserted dummy byte

ResetHandler: ; In the original ROM, this symbol was at address $C000; now it's at $C001.
    CLD
    SEI
...
```

If we merely insert a byte, the ROM will become one byte too big. We have to _delete_ a
byte as well, preferably right near the end of the ROM, before the three standard vectors (which must always
be the last six bytes). If we are lucky, there are some unused _padding_ bytes around that location,
but I've found this to be rare:
```
.DB $FF,$FF,$FF,$FF,$FF,$FF ; Yay, we can just delete an unused byte

.DW NMIHandler   ; Must always reside at address $FFFA
.DW ResetHandler
.DW IRQHandler
```

If there is no padding to steal from, we can work our way backwards from the tail, looking for a piece of
data or code that can be shortened by one byte without breaking the game. A good candidate is a
variable-length data payload where the format is well understood.

The relocation test is a perfect use case for a _mod_. You can ask an LLM to create it ("create a relocation test mod for balloon_fight").

Once the relocation test ROM is built, you (or an LLM) can play it in an emulator to check if the game still
works. If it locks up or glitches, it means that there are still some parts that are wired to the
original addresses. Even if the game plays OK, you can't be sure that everything is 100% relocatable 
without exercising every codepath and asset of the ROM. If you're lucky, there is an .fm2 movie recording of the game on https://tasvideos.org/ which can be used to validate the mod in FCEUX. (Tip: Use a Lua script that calls `emu.frameadvance()` in a tight loop, then most movies can be played through in a few seconds.)

For ROMs that use bank-switching, testing relocation is not as straightforward. Each program will use some form of Application Binary Interface (ABI) to transfer control to a switchable bank. This can for example be achieved by using a _trampoline_: A jump instruction that's placed at a fixed offset in the ROM bank, that jumps to the actual implementation of a subroutine. If the address of the trampoline shifts, the program will break unless the ABI is adjusted accordingly. In other words, additional care is needed for testing relocation, and you might want to do it one bank at a time.

## Bootstrapping a project

You can ask the LLM to do this ("create a new project called balloon_fight", then follow the instructions), but let's briefly look at what it takes to stand up a new project.

### Scaffolding

_Scaffolding_ creates a folder structure for the new project (the game we want to reverse engineer).

```
make project-init PROJECT=<slug>
```

_slug_ should be an identifier you choose based on the game, like `balloon_fight` or `ice_climber`.

The script will create the following folder structure:

```
  projects/<slug>/
  ├── asm/                                  # program code will live here
  ├── reference/                            # you will put the original .nes ROM here
  ├── build/                                # assembler output
  └── docs/
      ├── reverse_engineering/
      │   └── inventory/                    # KPI configs + bookkeeping CSVs
      ├── crosswalk/                        # external term ↔ internal symbol map
      └── game_reference/{manuals,faqs,metadata}/  # you can put reference documentation here
```
Most folders are empty, except for some that contain documentation stubs/placeholders and empty ledgers. There is also a `project.conf` file and `kpis.conf` file with default settings.

### Intake

With the project folder structure in place, the next step is to produce a _disassembly_
of the original ROM. Drop the ROM (defaults to `<slug>.nes`) in the project's
`reference/` folder, then run

```
make project-regenerate-asm PROJECT=<slug>
```

The disassembly is a textual representation of the whole ROM.
All the bytes have been translated to instructions and data blobs, in
a best-effort way. The disassembly doesn't convey any game semantics; there are
no meaningful symbolic names, and only raw addresses and (hex) literals.
All data are represented as arrays of raw bytes. No ordinary human can look at the disassembly and tell you which game it is.
Here's a preamble to give you an idea of what it can look like:
```
.ORG $C000

LC000:
.DB $01,$4C,$B8,$E3,$94,$00,$ED,$DF

LC008:
.DB $41,$59,$C7,$CA,$D3,$D7,$E6,$F4

LC010:
    CLD
    SEI
    LDA #$10
    STA $2000
    LDX #$FF
    TXS
LC01A:
    LDA $2002
    BMI LC01A
```

There are many thousand lines more like that (in a single file). The disassembly becomes "Version 0" of the reverse engineered source code.
It is the starting point for discovering semantics, and immediately lets us quantify many aspects that clearly lack semantics. After many iterations and refinements, this document will have metamorphosed into beautiful, context-rich,
self-documenting code and data.

A crucial property of the disassembly is that it must be possible
to feed it back into an assembler to produce a new ROM image that is
identical to the original program ROM _R0_:

> assemble(disassemble(R0)) == R0

For NES projects, I use a disassembler called [NESrev](https://github.com/khansen/nesrev) that produces
output which is compatible with the [XORcyst NES assembler](https://github.com/khansen/xorcyst).
The NESrev disassembler uses a simple form of static analysis to try
and infer which bytes in the ROM are code and which are data. All codepaths
are traced from the Reset, NMI (Non-Maskable Interrupt), and IRQ handlers (whose addresses are always at a fixed position in the ROM). Bytes of the ROM that aren't
reached from any of these entrypoints by following _explicit branch instructions_
are considered data. However, games often use _jump tables_ or other _indirect dispatch_ techniques
(such as code pointers embedded in instruction operands) that can cause NESrev to
incorrectly classify parts of the ROM as data when they are in fact code. Therefore it's important to inspect NESrev's output for suspicious
mis-classifications, to weed those out in this early phase. The `project_hidden_code_scan.sh` script can help with that; it scans data blobs in the disassembly for byte sequences that _look_ like code. NESrev can be fed with the location of jump tables
and known code sections in the ROM, so that they are processed appropriately. The disassembly process can therefore require some iterations; decoding one jump table can lead to the discovery of new tables that are used to dispatch from entries in the first, and so on. (A capable model can drive the whole intake process without human assistance.)

(It's been brought to my attention that there's a Code/Data Logger feature in the FCEUX NES emulator, but I haven't tried to incorporate it into the process described here.)

NESrev does not attempt to discover data pointers embedded in data blobs or in instruction literals. There is a script, `embedded_pointer_audit.py`, that can detect some (arrays of) pointers by using heuristics. Any remaining pointers must be discovered by the operator as part of semantic analysis.

Another crucial property of the disassembly is that it must use
_labels_ instead of raw addresses. This way, the results
from semantic analysis can readily be applied to the code, by
renaming labels. As a bonus, the code is inherently _relocatable_ (position-independent).
NESrev uses a convention of naming labels `L<address>`, encoding the
original address in the name (as seen in the
disassembly snippets above).

### Warning baseline

As part of intake, a `WARNING_BASELINE.txt` file is created. This file lists the assembler warnings that are produced when assembling the initial disassembly. Typically, these are unused label warnings, which could be because not all label references have been discovered yet, or because a label is genuinely unused. `WARNING_BASELINE.txt` must be kept in sync (warnings removed or updated) so that it always reflects the current (expected) warning output.

### Intake done

At this point, we should have a surgical disassembly with a (hopefully, roughly) clean separation between code and data. We have relocatable labels (although there could still be hardcoded addresses and sizes lurking around). The disassembly reproduces the original program ROM exactly. The disassembly is still fully opaque (no semantics).

## Using reference documentation

The official instruction manual, as well as walkthroughs and strategy guides,
are great resources for learning a game's language: The names of enemies, items, levels, and so on, and the rules (scoring, for example). In Popeye, there's Olive Oyl, Brutus, and spinach. In Ice Climber, there's Topi, Nitpicker, Polar Bear, and Condor. In the Ice Climber bonus stages, you collect vegetables. In Balloon Fight, there are balloons that pop, and so on. In reverse
engineering, we should use this information to recognize that a piece of code (and data it accesses) looks to be associated with a concept or entity in the game. The reverse engineered code should use words from the game's 
official vocabulary, not invent new names. Otherwise the code cannot possibly be
self-documenting. You want to be able to search the code and the technical documentation for a term from the manual. Moving to the next phase of the process without this crucial information would severely hamper the potential of the project. A "Balloon Fight" project without balloons might as well be called "Joust clone".

There is another type of reference documentation that you may be able to obtain: Technical documentation about the game's internals. Maybe someone already did some work in reverse engineering level data, for example. Since I previously reverse engineered Metroid's data formats and password system, and did a partially commented disassembly, I could drop some artefacts from those projects into the `docs/` folder at the start of the project. This is just nice-to-have if you already have the information readily available, and it's not something I've done in any projects so far (also because I wanted to test how well an LLM can figure everything out from scratch).

To make reference documentation available to the LLM, put the documents (such
as a PDF scan of the manual and a guide from https://gamefaqs.com) in the project's `docs/game_reference/` folder. The LLM can analyze the files and use them to build a `MANUAL_TERMS.md` file and `TERMINOLOGY_CROSSWALK.md` file, which will become key resources for the semantic work.

Once a) the project can be built from the "clean" disassembly to produce a ROM
that's identical to the original, and b) the game's terminology has been recorded, the bootstrapping phase is over and the  _real_ reverse engineering process (fun) can begin. But first, let's look at some cool features of the XORcyst assembler, as they are key enablers for an effective process.

## Tooling that supercharges the process

When I put the LLM to work on reverse engineering the first game, it soon became clear that the process
could benefit greatly from a few additional features in the XORcyst NES assembler. Instead of only producing
the binary ROM file (object file) as output, the assembler can now produce additional artifacts that are used to inform the mechanical gates as well as support semantic analysis and operations on the code. I had an LLM spec and implement the features, and then validated them in the reverse engineering loop.

LLMs prefer to work with structured data, so JSON is supported as output format.

The process _can_ work OK without such first-class reverse engineering-focused tooling features, but that puts a burden on the operator; they have to do more heavy lifting to be able to perform reliable semantic analysis, and the supporting scripts will be more constrained (e.g., scripts have to resort to applying regexes over the source code). Since I'm the maintainer of both the NES assembler and disassembler used in these projects, I could quickly extend and adjust those tools as suitable.

### Program graph analysis

The assembler parses the program source code and internally creates an intermediate representation of the
program, called an Abstract Syntax Tree (AST). The AST, let's call it the _program graph_, goes through
a number of passes where it is validated and transformed, before the binary output (ROM) is created in the
final traversal. Normally, the in-memory program graph is simply discarded. But in our case, the graph is _the real product_. Many of the assembler features for reverse engineering revolve around providing access to the
program graph and analyses of it.

- The cross-reference (xref) file effectively contains the whole program graph in JSON format: Who calls who,
who reads and writes what.
- The data consumers report identifies data labels with direct consumers and clear displacement patterns.
After analyzing the consumers, the data can be understood.
- The index patterns analysis is useful for determining the shape of data tables.
- The address audit report answers what addresses haven't been symbolized.

### Listing file

The listing file shows how the source text translates to bytes in the output, and it
shows the addresses where the bytes are placed. Here is a snippet in plaintext format:
```
-------------------------------------------------------------------------------
LINE  ADDR  HEX BYTES     SOURCE CODE
-------------------------------------------------------------------------------
0001  C000                .ORG $C000
0573  C000                Reset:
0574  C000  D8                CLD
0575  C001  78                SEI
0576  C002                @@waitVblank:
0577  C002  AD 02 20          LDA PPUSTATUS
0578  C005  10 FB             BPL @@waitVblank
0579  C007  A2 00             LDX #0
0580  C009  8E 00 20          STX PPUCTRL
0581  C00C  8E 01 20          STX PPUMASK
0582  C00F  CA                DEX
0583  C010  9A                TXS
```
The listing file also contains a _symbol table_ that defines the address of each symbol.
Here is a snippet:
```
-------------------------------------------------------------------------------
SYMBOL TABLE:
-------------------------------------------------------------------------------
Reset              = $C000
Reset@@waitVblank  = $C002
Reset@@clearRAMLoop = $C01D
Reset@@initPostClearState = $C02B
MainLoop           = $C04F
MainLoop@@initAudio = $C05D
MainLoop@@updateFrame = $C060
MainLoop@@waitNMI  = $C06A
MainLoop@@spin     = $C077
NMI                = $C07D
NMI@@exit          = $C0AC
TryUpdatePlayerMovementFromBufferedRecord = $C0B6
TryUpdatePlayerMovementFromBufferedRecord@@jumpToResetMoveFlag = $C0BF
TryUpdatePlayerMovementFromBufferedRecord@@runBufferedMove = $C0C2
TryUpdatePlayerMovementFromBufferedRecord@@dispatchBufferedMoveStateStrip = $C0F3
TryUpdatePlayerMovementFromBufferedRecord@@useBufferedMoveState = $C12E
```

The listing can be used to diagnose _binary drift_ that was introduced
by a change to the source code. Binary drift is a common issue when transforming the code in non-trivial ways; an operator is likely to experience this several times per project. The listing can also be used to calculate insertion points of data labels, for example as part of converting a pointer table embedded in a data blob to a proper table of (relocatable) label references.

### File comparison

In support of verifying binary parity, the assembler
provides a set of options for comparing the candidate ROM (in memory) to the reference ROM (on disk). This capability could be built as separate tooling on top of the assembler, but having it as part of the assembler itself is very convenient.

### Performance improvements

A 128 KB ROM can turn into around 50000 (fifty thousand) lines of code. At such sizes, I noticed that the assembler took a long time to invoke -- up to half a minute, in fact! The assembler sits at the heart of the process and is invoked very frequently, therefore it must be (blazing) fast. I got an LLM to profile the application and fix the main bottleneck, and the next one, and so on, until there were diminishing returns. By the end, the running time had been reduced to a few hundred milliseconds (two orders of magnitude faster than the starting point). I expect having to revisit this topic once even larger ROMs are targeted.

### FCEUX .nl files

The assembler can output .nl ("NameList") files that FCEUX uses for symbolic debugging. One limitation is that .nl files don't support overlays for RAM addresses. They do not support symbolic names for constants (instruction literals) either. But it's still pretty cool to be able to debug a game with most of the symbols carried over from the source code.

## Capturing NES hardware semantics

While it's true that all games have their own unique semantics that must be discovered "the hard way" through the reverse engineering loop (with the support of game reference documentation), they all run on the same NES hardware. This section shows how operators can utilize general knowledge of the hardware to symbolize specific addresses and values. Since it doesn't require any per-game semantic analysis, this is a quick win. The names and process can be standardized across projects (see the `ASM_STYLE.md` playbook for the full reference). All of these "recipes" for introducing hardware-level semantics are layed out in the playbooks.

### Symbolizing memory-mapped I/O

On the NES, hardware registers for the PPU (Picture Processing Unit) and APU (Audio Processing Unit) are mapped to addresses in memory. For example, the PPUSTATUS
register is mapped to address $2002. The following instruction
```
    LDA $2002
```
reads the PPUSTATUS register. Such address references are safe to symbolize without further
analysis. E.g.
```
PPUSTATUS .EQU $2002

    LDA PPUSTATUS
```
The various bits of hardware registers have fixed meanings. In the original disassembly, you might see the following two instructions:

```
    LDA #$90
    STA $2000
```

This sets bits 7 ($80) and 4 ($10) of the PPUCTRL register (address $2000). By using symbols for the bitmasks, the code becomes
much more readable:
```
PPUCTRL               .EQU $2000
PPUCTRL_BG_TABLE_1000 .EQU %00010000
PPUCTRL_NMI_ENABLE    .EQU %10000000

    LDA #(PPUCTRL_NMI_ENABLE | PPUCTRL_BG_TABLE_1000)
    STA PPUCTRL
```

In other words, this `STA PPUCTRL` instruction selects background pattern table address $1000 and enables the NMI (Non-Maskable Interrupt).

The PPUCTRL register isn't possible to read; `LDA PPUCTRL` won't return what was last written to it. Therefore,
games typically store the value in a _shadow register_ in RAM. E.g.

```
    LDA #(PPUCTRL_NMI_ENABLE | PPUCTRL_BG_TABLE_1000)
    STA PPUCTRL
    STA $08     ; Just a normal RAM address.
```
Here, RAM address $08 is used as the PPUCTRL shadow register, and it too can be symbolized:
```
ZP_PpuCtrlShadow .EQU $08

    LDA #(PPUCTRL_NMI_ENABLE | PPUCTRL_BG_TABLE_1000)
    STA PPUCTRL
    STA ZP_PpuCtrlShadow
```

By using the shadow register, some bit(s) can be masked off or set later,
without disturbing the rest, like in this example:

```
    LDA ZP_PpuCtrlShadow
    AND #$FB
    STA PPUCTRL
    STA ZP_PpuCtrlShadow
```

$FB in binary is 11111011 -- the inverse of 00000100, which is the "VRAM address increment (1 or 32)" flag. It can be symbolized as follows:
```
PPUCTRL_VRAM_INC_32 .EQU %00000100

    LDA ZP_PpuCtrlShadow
    AND #~PPUCTRL_VRAM_INC_32
    STA PPUCTRL
    STA ZP_PpuCtrlShadow
```
(The `~` operator inverts all the bits in the operand.)

In other words, the `STA PPUCTRL` instruction will ensure that the VRAM address increment is set to 1 (not 32), while other PPUCTRL settings remain unaffected.

### Symbolizing sprite (OAM) memory access

Every game I've encountered so far stores sprite attributes in the RAM page $0200-$02FF, and
uses DMA (Direct Memory Access) to transfer the attributes to OAM (Object Attribute Memory) in the NMI handler.

Each sprite occupies four bytes of OAM:

|Offset|Field|
|------|-----|
|  0   | Y position |
|  1   | Tile  |
|  2   | Attributes |
|  3   | X position |

The addresses in the following disassembled instructions
```
    STA $0200
    STA $0201
    STA $0202
    STA $0203
```
can therefore be symbolized as follows:
```
RAM_OamShadowBase .EQU $0200
OAM_FIELD_Y       .EQU 0
OAM_FIELD_TILE    .EQU 1
OAM_FIELD_ATTR    .EQU 2
OAM_FIELD_X       .EQU 3

...

    STA RAM_OamShadowBase+OAM_FIELD_Y
    STA RAM_OamShadowBase+OAM_FIELD_TILE
    STA RAM_OamShadowBase+OAM_FIELD_ATTR
    STA RAM_OamShadowBase+OAM_FIELD_X
```
With semantic field offsets, the code is substantially easier to read.

The addresses in the following disassembled instructions
```
    STA $0204
    STA $0205
    STA $0206
    STA $0207
```
can be symbolized as follows:
```
OAM_SPRITE_STRIDE .EQU 4

    STA RAM_OamShadowBase+OAM_SPRITE_STRIDE+OAM_FIELD_Y
    STA RAM_OamShadowBase+OAM_SPRITE_STRIDE+OAM_FIELD_TILE
    STA RAM_OamShadowBase+OAM_SPRITE_STRIDE+OAM_FIELD_ATTR
    STA RAM_OamShadowBase+OAM_SPRITE_STRIDE+OAM_FIELD_X
```

However, at this stage it makes sense to move beyond mechanical symbolization and use
semantic analysis to determine what sprite is stored at offset $04. Many games use fixed offsets for certain (collections of) sprites.

Typically, games store a separate representation of game objects in RAM, and
then "render" their sprites to OAM shadow RAM (often using some variation of a "metasprite" data format). Symbolizing OAM field access
(OAM_FIELD_*) can make it easier to understand the role of the game object (source)
fields, by tracing backwards from the instructions that write the sprite fields.

Instead of using field offsets, a game might use absolutely indexed instructions to write the sprite fields. In that case, comments make the code more readable:
```
    STA RAM_OamShadowBase,X ; OAM_FIELD_Y
    INX
    STA RAM_OamShadowBase,X ; OAM_FIELD_TILE
    INX
    STA RAM_OamShadowBase,X ; OAM_FIELD_ATTR
    INX
    STA RAM_OamShadowBase,X ; OAM_FIELD_X
```

## Similarities across games

In the NES days, there weren't shared libraries of code in the modern SDK (Software Development Kit) sense. However, games were not developed in a vacuum. Some teams at Nintendo and second-party developers (like HAL) worked on several games. Just like developers of today, they knew how to copy and paste code! Starting from scratch in every game wouldn't be cost-effective; instead, developers could copy things from previous games that worked well and that were relevant for the new game, and adjust the code as needed. You probably wouldn't be shocked to learn that "Donkey Kong Jr. Math" borrows a lot of its implementation and assets from "Donkey Kong Jr.".

As more and more projects are completed, studying _prior art_ becomes an increasingly important and effective technique -- a virtuous circle. The likelihood of finding some existing matching code (possibly entire subsystems, such as audio drivers), where a lot of effort was already spent on figuring out semantics, keeps getting bigger. As a result, the operator can focus more on game-specific semantic analysis from the get-go.
The following subsections describe some noteworthy similarities I've come across.

### Dispatch techniques

Pretty much every game uses one or more ways of indirectly dispatching code by indexing a jump table. The most common way is dispatching via an _in-line jump table_:
```
ProcessGameMode:
    LDA ZP_GameMode
    JSR DispatchInlineJumpTable
.DW GameMode_InitPhase
.DW GameMode_SpawnEnemies
.DW GameMode_TransitionToPlay
...
```
The jump table is stored _in-line_ (anonymously) immediately following the `JSR DispatchInlineJumpTable` instruction. `DispatchInlineJumpTable` pops the return address minus 1 off the stack, adds 1 to get the address of the jump table, fetches the 16-bit address at (JumpTable + Accumulator*2), and jumps to it.

A variation of in-line dispatch is to dispatch through an RTS instruction instead of the indirect-form JMP. The target address _minus one_ is pushed on the stack, high byte first, and then an RTS instruction is executed. To avoid having to adjust the target address at runtime, the jump table should contain target addresses minus one -- preferably also in big-endian form, since the high byte will be accessed first:
```
ProcessGameMode:
    LDA ZP_GameMode
    JSR DispatchInlineJumpTableRts
.DB >(GameMode_InitPhase-1), <(GameMode_InitPhase-1)
.DB >(GameMode_SpawnEnemies-1), <(GameMode_SpawnEnemies-1)
.DB >(GameMode_TransitionToPlay-1), <(GameMode_TransitionToPlay-1)
```

By defining a few helper _macros_, the table definitions can be made cleaner:
```
; Define big-endian word
.MACRO DW_BE value
.DB >(value), <(value)
.ENDM

; Define entry in RTS-style jump table.
.MACRO RTS_SLOT addr
DW_BE (addr)-1
.ENDM

ProcessGameMode:
    LDA ZP_GameMode
    JSR DispatchInlineJumpTableRts
RTS_SLOT GameMode_InitPhase
RTS_SLOT GameMode_SpawnEnemies
RTS_SLOT GameMode_TransitionToPlay
```

### PPU packets and streams

The _PPU packet_ is arguably the most ubiquitous graphics-related data format used in Nintendo's games. A PPU packet defines a string of bytes to be written to video RAM via PPU I/O registers. This is the primary mechanism that most games use to write data to _nametables_ (NES screen definitions), _attribute tables_ (palette selectors), and palette RAM.

The first two bytes of a _bog-standard_ PPU packet hold the starting address in VRAM, in big-endian order. The third byte contains two control bits and a 6-bit count. The fourth and subsequent bytes contain the payload (actual bytes that will be written to VRAM).

One control flag (bit 7) specifies the PPU address increment setting (1 or 32); this setting is copied to the corresponding bit in the `PPUCTRL` register. The other control flag (bit 6) specifies whether the data is run-length encoded (RLE). If yes, the payload consists of a single byte that is repeated {count} times. If RLE is not used, the payload consists of {count} bytes.

Here's a PPU packet for writing the string $CA, $FE to address $2042:
```
.DB $20,$42,$02,$CA,$FE
```

Here's a PPU packet for writing the string $CA, $CA, $CA to address $2184:
```
.DB $21,$84,PPU_PACKET_RLE|$03,$CA
```

There are two ways of defining PPU packets: Statically and dynamically. Static PPU packets are defined verbatim in the ROM. They are commonly used to build title screens and other "ad hoc" screens (but not large (multi-screen) levels).

Dynamic PPU packets are constructed in RAM on-the-fly. Since it's only safe to write to video RAM during the vertical blanking (VBlank) interval when the display is enabled, a common technique that NES programs use is to write the PPU packets to regular RAM during the frame handler (game loop), and then flush the packets to video RAM as one of the first actions in the NMI handler. Regardless of how level data is stored in the ROM (e.g., a fixed-size meta-tile format like in Mega Man, or a variable-sized "structure" format like in Metroid), the game engine will ultimately translate level data to PPU packets -- the low-level graphical "display lists".

A nametable is 32 by 30 tiles (bytes). The attribute table is another 64 bytes. Palette RAM is 32 bytes. For building a title screen, you'll need more than one PPU packet (the maximum length of one packet is 63 bytes). A common technique is to clear the whole nametable to a solid/blank tile via a dedicated subroutine, and then write a series of PPU packets ("strips") for the spans that have content. It would be cumbersome if each packet had to be written separately by the orchestrating code. Enter _PPU packet streams_! A PPU packet stream is a series of _in-line_ packets (no pointer indirection), terminated by a zero byte. Example:
```
.DB $20,$42,$02,$CA,$FE            ; The first packet.
.DB $21,$84,PPU_PACKET_RLE|$03,$CA ; The second packet.
.DB $3F,$00,$04,$0F,$04,$07,$19    ; The third packet.
.DB 0 ; The end of the stream.
```

Notice that using a zero byte as stream terminator only works because the VRAM addresses are stored in big-endian format. It means PPU packets can't target VRAM addresses $0000-$00FF, but that's usually fine (games with CHR-RAM use a different mechanism to transfer tile data).

PPU packet streams are also useful for dynamic construction of packets; it's not uncommon that a game engine wants to update multiple, non-contiguous strips of nametable data in a single frame, and possibly also attribute table data and/or palette data. Therefore it's common to have a RAM buffer that can hold a stream of packets. The entire stream is flushed each VBlank, and then the buffer cursor is reset. A buffer size of 128 bytes should be more than enough (any bigger, and there might not be enough time to flush all data within the VBlank interval).

PPU packets strike a fair balance between simplicity and space efficiency. The format is so simple that static packets can be written by hand. The code for processing (decompressing) packets has minimal overhead. Some games, like Kid Icarus, additionally implement more advanced packet formats.

### Objects

Most games have some sort of (animate) object system. Each object can have a number of state variables associated with it, such as X and Y position, size/extent, animation frame, behavior flags/script, and timers. A typical way of representing object state is as an array of structures with fixed-offset fields (layout), very similar to sprite (OAM) records. Some games use one generic object structure with a type discriminator field, while others maintain different records (layouts) for different kinds of object (players versus enemies versus projectiles, for example). Here is an example of what an object layout can look like:
```
RAM_ObjectSlotBase           .EQU $0700
OBJECT_SLOT_SIZE             .EQU $20
OBJECT_SLOT_FIELD_Y          .EQU $00
OBJECT_SLOT_FIELD_TYPE_STATE .EQU $01
OBJECT_SLOT_FIELD_MOTION_CODE .EQU $02
OBJECT_SLOT_FIELD_X          .EQU $03
OBJECT_SLOT_FIELD_X_VELOCITY .EQU $04
OBJECT_SLOT_FIELD_Y_VELOCITY .EQU $05
...
```

The symbolized code then becomes easy to read:
```
    LDX #(1 * OBJECT_SLOT_SIZE) ; Second object
    LDA #100
    STA RAM_ObjectSlotBase+OBJECT_SLOT_FIELD_Y,X
    LDA #200
    STA RAM_ObjectSlotBase+OBJECT_SLOT_FIELD_X,X
```

### Audio

Most of Nintendo's early games use variations of the same audio code and data formats. At a high level, the program code sets request bits that correspond to the various pieces of music and sound effects. The audio driver decodes per-channel "token streams" that hold pitch, duration, volume, and other properties; the tokens are translated into writes to the audio hardware registers.

## Discovering embedded pointers

One of the biggest threats to the completeness of a project is the risk of _unsurfaced embedded pointers_. If left undetected, they (and the things they point to) will remain raw bytes rather than label references and semantic definitions. These pointers can hide in code or in data and they are invisible to binary parity checks. There are ways to smoke them out. The weakest (but sometimes effective) way is by applying plain pattern matching; for example, a typical trait of pointer tables is that the high byte is in the range $80-$FF and that it is monotonically increasing across entries (in little-endian format):
```
.DB $4E,$C2,$89,$C2,$B5,$C2,$04,$C3,$3B,$C3,...
```
Obviously, this check can produce false positives, and it will only catch a subset of real pointer tables. (Similar heuristics can be used to detect de-interleaved pointer tables, i.e. where the low bytes and high bytes are stored in separate tables.) But you can argue that it's better to explicitly check and rule out any candidates than to risk leaving real pointers undetected. The check is cheap to perform on any project and it is purely mechanical, which makes it easy to incorporate into the standard process.

The better, reliable way of detecting embedded pointers is through semantic analysis, which is the operator's principal duty. There are two common scenarios to look out for: Pointers in instruction operands, and pointers in data structures. Let's say the operator has understood that a subroutine takes the X and Y registers as input and that the register pair defines a pointer where data are read from:
```
; X/Y hold low/high pointer bytes for a zero-terminated PPU packet stream written immediately to PPU.
WritePpuPacketStreamFromXY:
    STX ZP_PpuStreamPtrLo
    STY ZP_PpuStreamPtrHi
    ...
    LDA [ZP_PpuStreamPtrLo],Y
    ...
```
The obvious next step is to symbolize the operands at all call sites. E.g.
```
    LDX #$CA
    LDY #$FE
    JSR WritePpuPacketStreamFromXY
```
can become
```
    LDX #<TitleStartupPpuPacketStream
    LDY #>TitleStartupPpuPacketStream
    JSR WritePpuPacketStreamFromXY
```
Here, the operator not only replaced the hardcoded pointer with label references, but gave the label a semantic name based on the context in which it is used (title screen initialization). Furthermore, since the shape of the data is known from how they are consumed, the operator can proceed to format the data for readability. The operator used the assembler listing to figure out where the label should be inserted into the source code.

The second common scenario for embedded pointers is that they hide cunningly in data blobs (strings of raw bytes). The number one rule of data blobs is:  Never just name a blob and be done with it. Always analyze how a blob is read, so that it may be promoted to a semantic structure, and pointers within that structure may be unraveled. For example, an enemy (type) definition might contain a pointer to a _behavior script_ (subroutine), as well as pointers to _animation frames_ and _hit boxes_.

While the process scripts can't reliably detect that all embedded pointers have been discovered, the operator is required to populate two inventory files (`data_extent_assertions.csv` and `data_blob_dispositions.csv`) as a way of recording that blobs have actually been studied and that their contents are well understood. Embedded pointers should be recorded in `embedded_pointer_targets.csv`. This effectively reduces the blind spots of the mechanical gates. For a (supposedly) mature project, it's a red flag if the data inventory files aren't fully populated.

## Label localization

Local (or _private_) labels are code labels that are only visible between two global (or _public_) labels. They allow branch targets to be contained inside a subroutine; no code outside the subroutine can jump directly to them. Since a local label name only has to be unique within its scope, the same name can be used in multiple scopes; this relieves the programmer of the burden of coming up with globally unique names for all labels in the program. Just like global labels, local labels should have semantic names that make the code easy to read. In the following example, each subroutine has its own local label, `@@loop`:

```
FooTheBar:
    LDX #1
@@loop:
    DEX
    BNE @@loop
    RTS

BarTheFoo:
    LDY #1
@@loop:
    DEY
    BNE @@loop
    RTS
```

The NESrev disassembler currently doesn't analyze the control flow to figure out which labels could be made local (although it probably could/should!); all labels in the initial disassembly are global, and are guaranteed to be unique because the address is part of the name.

```
LC012:
    LDX #$01
LC014:
    DEX
    BNE LC014
    RTS
LC019:
    LDY #$01
LC01B:
    DEY
    BNE LC01B
    RTS
```

It is up to the operator to transform the code to the localized form (mechanical work) with appropriate label names (semantic work).

## Magic numbers, computed numbers, and plain numbers

_Magic numbers_ are literal values whose meaning are non-obvious to the reader. Example:
```
    LDA RAM_PlayerEquipmentFlags
    AND #$10
    BEQ @@maybeBomb
```
In this context, $10 is a bitmask that indicates whether the player has a certain power-up. By symbolizing this constant, the code becomes much more readable:
```
EQUIPMENT_FLAG_MARU_MARI .EQU %00010000
...
    LDA RAM_PlayerEquipmentFlags
    AND #EQUIPMENT_FLAG_MARU_MARI
    BEQ @@maybeBomb
```
Note that not only was the constant symbolized, but the value was changed to binary (base 2), since that's more readable as a mask.

Can you spot a readability and maintenance issue with the following code?
```
InitUiSpriteSlotPairFromTemplate:
    LDX #10
@@copyLoop:
    LDA UiSpriteSlotPairInitTemplate,X
    STA RAM_UiSpriteSlotBase,X
    DEX
    BPL @@copyLoop

UiSpriteSlotPairInitTemplate:
.DB $3C,$C6,$01,$18,$00,$00,$00,$00,$20,$00,$00
```
10 is the index of the last element of the UiSpriteSlotPairInitTemplate array, but it's hardcoded. Better to compute the index from the actual end of the array:
```
InitUiSpriteSlotPairFromTemplate:
    LDX #(UiSpriteSlotPairInitTemplateEnd-UiSpriteSlotPairInitTemplate-1)
@@copyLoop:
    LDA UiSpriteSlotPairInitTemplate,X
    STA RAM_UiSpriteSlotBase,X
    DEX
    BPL @@copyLoop

UiSpriteSlotPairInitTemplate:
.DB $3C,$C6,$01,$18,$00,$00,$00,$00,$20,$00,$00
UiSpriteSlotPairInitTemplateEnd:
```
Now it's obvious what the initial value of X is, and it's obvious that the calculation is correct. If the size of the array were ever to change, the initial value of X would be updated to match it.

There are numbers that don't have to, and even shouldn't, be symbolized. 0 and 1 are often good candidates to exclude from symbolization (but there is no universal rule). After semantic analysis, the operator can choose not to symbolize a number; then that decision should be recorded in `constant_magic_allowlist.csv`. The `project-maturity-check` script will warn if _all_ constants in a project have been symbolized and `constant_magic_allowlist.csv` is empty, since that's a symptom of over-symbolization.

## Dynamic analysis

There is a trace template runner and Lua script for FCEUX that can be adopted for each project. Each trace needs a setup that puts the game in a state where it's ready to be traced. An effective way of achieving this is to create a _mod_ that allows easy triggering of the behavior that we want to trace. For example, we can create a mod that adds a Sound Test screen to the game, or a mod that starts the game in a given level. I've successfully applied this approach to several games.

For "Urban Champion", I noticed there was a lot of padding (unused space) near the end of the ROM. This is a perfect place to implement a Sound Test. I had an LLM implement it (yes, _vibe coding_ new features in an existing program). At the title screen, the Sound Test can be entered by pressing a special button combo. A simple UI lets me trigger all the audio programs (music and sound effects) in the game, without having to prepare multiple scenarios/variations.

A middle ground between a hardcoded mod (that changes some fixed bytes) and a "dynamic" mod (with a custom UI) is to create a trace script that accepts one or more parameters that are used to patch the mod before capturing the trace. (This was actually a strategy that the LLM came up with when we were tracing audio request bits in Metroid.)

Another great use for dynamic analysis is to have an LLM try to find exploits and bugs. For example, I had the LLM try to find bugs related to pausing and unpausing a game at opportune times; it first did a static analysis to find promising scenarios, and then was able to test hundreds of runs in a few seconds.

## Example pass

After intake, you can just tell the LLM to "do the next pass". To demonstrate what actually happens, let's manually perform all the steps of the first semantic pass on Zelda (immediately after intake).

```
make project-next-pass PROJECT=zelda
```
The command surfaced the label L7FFAC as a high-fanout callable corridor. Reading the surrounding code shows that it sits next to the reset vector and MMC1 setup, so the pass can be broadened from “one helper” to the coherent reset/MMC1 serial-register corridor.

Zelda has no working notes yet, so there is no durable deferred instruction to apply.

We start the pass:
```
make project-pass-start PROJECT=zelda PASS=1 TARGET=L7FFAC \
    CORRIDOR="fixed-bank reset and MMC1 serial register helpers" ...
```

The core evidence is mechanical:
- Reset vector -> L7FF50
- L7FF98 writes A serially to $8000 five times
- L7FFAC writes A serially to $E000 five times

Now we make the edits to the code:
- Add canonical PPU/MMC1 constants (as per `ASM_STYLE.md`).
- Rename L7FF50 to Reset.
- Rename fixed-bank helpers to WriteMmc1ControlRegister and WriteMmc1PrgBankRegister.
- Rename bank-1 mirrors to WriteMmc1ControlRegisterBank1 and WriteMmc1PrgBankRegisterBank1.
- Localize the reset VBlank wait loops.
- Replace touched raw hardware addresses/immediates with constants.

We also update codeentries.txt, ONBOARDING.md, renames.csv, generated inventories, and the scorecard to reflect the changes made to the code.

Next, we update the inventory and verify everything:
```
make project-inventory PROJECT=zelda
ALLOW_UNRESOLVED_LXXXX=1 make project-verify PROJECT=zelda
```
Until all labels in the project have been renamed from LXXXX to something semantic, ALLOW_UNRESOLVED_LXXXX=1 is required to produce a warning instead of an error. The key output:
```
OK: warning baseline unchanged
OK: binary identity preserved
WARN: 3353 distinct LXXXX/LXXXXX labels (8015 refs); allowed
OK: no UNK_* symbols
OK: raw-address KPI gate passed
OK: constantization KPI gate passed
OK: no stale raw-address comments found
OK: data-label documentation KPI gate passed
```

We perform a self-review:
- Inspect the final diff as if reviewing someone else’s PR.
- Check that names are semantic and scoped correctly.
- Check no stale raw addresses/comments were introduced.
- Check docs/inventories match the actual changed symbols.
- Rerun the exact verification mode that will be claimed green.

Everything looks good, so we can close the pass:
```
make project-pass-closeout PROJECT=zelda PASS=1 VERIFY_MODE=relaxed \
    FOCUS="reset and MMC1 serial register helpers" \
    NOTES="Named Reset plus fixed-bank and bank-1 MMC1 serial writers; ..."
```
A row is added to the project's PROGRESS_SCORECARD.md.

Finally, we commit the pass:
```
git commit ...
```
```
git show --name-status --format=""
M       projects/zelda/asm/zelda.asm
M       projects/zelda/config/nesrev/codeentries.txt
M       projects/zelda/docs/reverse_engineering/ONBOARDING.md
M       projects/zelda/docs/reverse_engineering/PROGRESS_SCORECARD.md
M       projects/zelda/docs/reverse_engineering/inventory/branch_literal_sites.csv
M       projects/zelda/docs/reverse_engineering/inventory/constants_catalog.csv
M       projects/zelda/docs/reverse_engineering/inventory/renames.csv
M       projects/zelda/docs/reverse_engineering/inventory/unknowns.md
```

After a few hundred more passes like this one, Zelda should be in great shape!

## Improving the code

No program, even one made by Nintendo, is perfect. Many of the items mentioned in this section can be found by the static analysis script (`make project-static-analysis`).

### Micro-optimizations

Finding ways a game's code could be optimized for size and/or speed is a fun exercise. Once the whole program is relocatable, we could even create an _optimization mod_ to collect such improvements. In this section I'll describe a few micro-optimizations ("peephole" optimizations) that could have been applied to real games I've studied. These are short, idiomatic instruction sequences that can be used without having to redesign or reimplement an algorithm.

#### Tail-call optimization

`JSR <label>` followed by `RTS` can be replaced with `JMP <label>` if the callee doesn't manipulate the stack. This saves one byte and 9 CPU cycles (6+6 versus 3).

```
    JSR PollSingleJoypad ; can be replaced by JMP
    RTS                  ; can be deleted
```

#### Waiting for VBlank

The canonical way to wait for the next VBlank is to poll the PPUSTATUS register until bit 7 is set.
The 6502's LDA instruction affects CPU status flags; bit 7 of the loaded value is copied to the
N (Negative) flag of the status register. Therefore, the minimal polling loop is

```
    @@waitVBlank:
    LDA PPUSTATUS
    BPL @@waitVBlank
```

However, not all games use this implementation.
"Ice Climber" implements the same loop like this:

```
    @@waitVBlank:
    LDA PPUSTATUS
    ASL
    BCC @@waitVBlank
```

The register is shifted one bit left, which effectively copies the original bit 7 to the Carry (C) flag of the status register.
If the Carry flag is clear, it means bit 7 of PPUSTATUS was zero, which means the loop should continue.

Technically, it achieves the same result as the idiomatic LDA + BPL version, but with one extra instruction (one byte), and two extra cycles per iteration
(not that the cycle count matters, in this case).

Donkey Kong, Donkey Kong Jr., Excitebike, and Popeye all use a redundant AND instruction (two bytes) to test bit 7:

```
@@waitVBlank:
    LDA PPUSTATUS
    AND #%10000000
    BEQ @@waitVBlank
```
Possibly, the developer(s) didn't know that the LDA instruction affects status flags. (On most CPUs, it's not common that _move_-instructions have such side effects.)

#### Loop invariants can be hoisted

If a constant value is loaded to a register inside a loop, and the register isn't modified subsequently, the load can be moved out of the loop (_hoisted_). Here's an example from Kid Icarus:
```
@@clearEntryBuffer:
    LDA #0
    STA RAM_PasswordEntryCharBuffer,X
    DEX
    BPL @@clearEntryBuffer
```
The following optimized version achieves the same result (clearing the buffer), but uses two CPU cycles less per loop iteration (or more precisely, the cost of the single `LDA #0` instruction is amortized over all iterations):
```
    LDA #0
@@clearEntryBuffer:
    STA RAM_PasswordEntryCharBuffer,X
    DEX
    BPL @@clearEntryBuffer
```

#### Redundant comparison to zero

`CMP #0` is redundant when the Zero (Z) flag or Negative (N) flag of the CPU status register already
indicates whether the last loaded value was zero or negative, such as after an LDA or TYA instruction,
_and_ the subsequent code doesn't rely on the Carry (C) being set to 1.
This wastefulness is surprisingly widespread across several games.

```
    LDA ZP_ScrollY
    CMP #0
    BNE @@somewhere
```
Again, it could be that the developer(s) didn't know that the LDA instruction affects status flags.

#### Redundant Exclusive OR with zero

Donkey Kong Jr. performs an exclusive OR with zero, which is equally redundant to `CMP #0`.
```
    LDA ZP_Stage1SnapjawStateBase,X
    EOR #$00
```

#### Unconditional relative branch optimization

The 6502 CPU doesn't have an unconditional relative branch instruction. The JMP instruction takes an absolute 16-bit address (two bytes), whereas relative branch instructions take a signed 8-bit offset (one byte). Often, the state of one or more CPU flags is known, so that a relative branch instruction effectively becomes unconditional. Here's a code snippet from Kung Fu:
```
    CPY #COMBATANT_SUBSTATE_ACTIVE
    BEQ @@tickActiveCounter
    JMP @@advanceMoveSubstate
```
Here's what the code looks like after applying the optimization:
```
    CPY #COMBATANT_SUBSTATE_ACTIVE
    BEQ @@tickActiveCounter
    BNE @@advanceMoveSubstate ; branch always
```
This only works if the branch target is within reach of the signed 8-bit displacement.

### Bugs

Even more exciting than micro-optimizing code is finding and documenting bugs in the code. Early NES games don't have many bugs, but there are some very interesting defects (that don't necessarily manifest as user-visible issues). The following subsections cover some of my curated favorites.

#### Donkey Kong 3: Coconut-spawn seed never advances with the round

In Donkey Kong 3, there is a piece of code that wants to use a different _coconut-spawn seed_ when the round number is 6 or greater. The seed determines the maximum rate at which Donkey Kong can drop coconuts. The intention was that the game should become more difficult in higher rounds, by using a seed that gives a faster rate. The code calculates a 2-bit index (range 0..3) into a table of seeds. In pseudo-code:
```
    TableIndex = GameType * 2 # type A = 0, B = 1
    If RoundNumber >= 6 Then
      TableIndex = TableIndex + 1
    End
```

Unfortunately, the implementation has a bug. Can you spot it?
```
    LDA ZP_RoundNumberBcd
    CMP #6
    LDA ZP_GameTypeIndex
    ASL
    TAY
    LDA Stage2CoconutCadenceSeedByGameType,Y
    STA ZP_Stage2CoconutCadenceSeed
    RTS

Stage2CoconutCadenceSeedByGameType:
.DB 0,3,3,5
```
`CMP #6` sets the carry flag when `A >= 6`. The programmer thought that the subsequent `ASL` instruction would shift the carry flag into bit 0 of the accumulator, while also multiplying the game type discriminator by two, to produce the index value. Unfortunately, that's not how the 6502 CPU's `ASL` instruction actually works; it always shifts the value 0 -- not the carry flag -- into bit 0 of the accumulator. So the round number check is effectively a no-op. In practice, it means that Game A always uses 0 as the seed (not 3 for higher rounds), and Game B always uses 3 (not 5 for higher rounds). Seed 0 corresponds to roughly 9.6 seconds per attempt, seed 3 to 6.4 seconds, and seed 5 to 4.3 seconds.

To get the intended result, use a `ROL` instruction instead of `ASL`. The Game Genie code ZZGKPN applies that patch.

I'm guessing this bug wasn't caught by play testers because the behavior isn't straightforward to test; whether Donkey Kong will _actually_ drop a coconut additionally depends on his position and on the player's score, not just the seed.

Interestingly, the Donkey Kong code has a redundant `CLC` instruction that is an indication of the same misunderstanding of how `ASL` works:
```
    TXA
    TAY
    CLC ; This is redundant!
    ASL
    ASL
    TAX
    LDA ZP_PlayerScoreHigh,X
```
In that case, however, the instruction is harmless (doesn't cause any bugs). Either the same programmer worked on both games, or Nintendo had a whole team of developers who skipped some _shifts_ in 6502 school.

#### Kid Icarus: Buffer overrun from clearing the wrong index register

Kid Icarus has a subroutine that means to clear the Y register before a loop, but clears the X register (which is unused in the loop) instead.
```
LoadSpritePalette:
    LDX #0 ; Oops! Should have been LDY
@@copyPaletteByte:
    LDA SpritePalette,Y
    STA RAM_SpritePaletteBuffer,Y
    INY
    CPY #16
    BNE @@copyPaletteByte
    RTS
```
It just so happens that when this subroutine is called, the Y register has value 16. So the code will read the 240 bytes that _follow_ the SpritePalette array and write them _past_ RAM_SpritePaletteBuffer, overwriting (corrupting) whatever data were there. Then Y wraps around to zero, and the actual palette is copied to the intended location. The RAM corruption does not cause any issues in practice (the affected area is scrolling-subsystem scratch that gets rebuilt afterwards), and therefore this bug went undetected.

#### Donkey Kong 3: Failing to differentiate power spray duration by game type

In Donkey Kong 3, there is a piece of code that supposedly wants to initialize the power spray timer according to the type of game (A or B). But both timer values
are identical.

```
    LDA #$74
    LDY ZP_GameTypeIndex
    BEQ @@setPowerSprayTimer
    LDA #$74 ; It's the same value as above!
@@setPowerSprayTimer:
    STA ZP_PowerSprayTimer
```
The value 74 hex corresponds to roughly 15.5 seconds. Maybe the programmer put the Game B value as a placeholder but forgot to adjust it later? This scenario could have been caught in play testing, but only if the testers were aware of the intended behavior. Most likely, the duration was supposed to be shorter in Game B. Or maybe the designers decided that they didn't want to apply this differentation after all, and instead of pruning the code, the programmer made the values identical.

#### Donkey Kong 3: Double negation in distance calculation

In Donkey Kong 3, there is a piece of code that wants to calculate the absolute Y distance between an object's current position and a target position (where the object should move towards). When the distance is negative (i.e., the target position is further down the screen than the object itself), the absolute (positive) value can be obtained by negating the difference. Unfortunately, there is a bug that causes negation to be applied twice, which means that the calculation effectively becomes a no-op:
```
    JSR NegateA
    ; Oops, this undoes the effects of NegateA
    EOR #$FF
    CLC
    ADC #1
```
It could have been due to a botched refactoring job (the intention was likely to replace the in-line negation code with a subroutine call). The corresponding handling of X distance does not have the same bug.

I haven't been able to capture this scenario in a runtime trace, because the pre-conditions needed to reach this codepath are quite strict. This could explain why the issue wasn't caught in play testing. The Y distance feeds an axis-lock check that suppresses X motion, so the practical effect of the bug might be that a Buzzbee enemy "wobbles" a bit along the X axis as it approaches its target position, instead of going straight; not a game-breaking behavior.

#### Kung Fu: START button stalls the floor-2/floor-4 intermission

I remember discovering this bug/quirk when I was about nine years old. In the intermission ("cutscene") between the second and third floor, pressing the Start button allows the game to be paused. When the game is paused, no timers, not even the intermission exit timer, are updated. Meanwhile, audio is still processed, so the pause jingle will play, as will Mr X's laugh sample, and it will keep playing if you repeatedly pause and unpause the game. A simple fix would be to ignore the Start button while the game is in "intermission mode".

#### Kid Icarus: The first, empty underworld room is an upgrade room

If you've played Kid Icarus, you must have wondered: Why is the first room of the first stage completely empty? It always intrigued me, and I'm still trying to find a plausible explanation. Was it a last-minute bug that regrettably made it into the production print? Was there an intention of having a way to unlock a secret in that room, perhaps after clearing the game? Or, the most boring explanation: Is it just a "tutorial door" that Nintendo put there so you'll know a door when you see one, and that you can enter doors by touching them?

Someone did already discover that the room is in fact an _arrow-power upgrade_ room; see for example Daniel Remar's FAQ https://gamefaqs.gamespot.com/nes/587380-kid-icarus/faqs/17485. The snag is that you need an _arrow-power qualification score_ (a hidden variable, not shown on the status screen) of at least 10000 points in order for the upgrade to appear. You gain hidden points by killing enemies and collecting hearts. Unfortunately, there seems to be no way to reach 10000 points that early in the stage. With the fully reverse engineered source code in hand, this topic can be explored from every possible angle. It became clear that the qualification score is scoped per life per stage: It does not survive any kind of transition -- death, an ordinary stage clear, or a full game finish -- because code that resets the score to zero is always executed on all paths. I've used an LLM to search extensively (statically and dynamically) for exploits that will allow the upgrade to be obtained without modifying the game, so far without success. But I had a lot of fun creating more than a dozen Game Genie codes that allow the upgrade to be obtained, each in their own novel way (patching an instruction or data byte).

## Working with LLMs

This section contains some reflections on experiences with using LLMs for reverse engineering.

Just because AGENTS.md and the playbooks give detailed instructions on how to handle every possible scenario doesn't mean the agent will care -- even if you plead that every bullet point is "mandatory". You can keep piling on additional rules every time the agent makes a mistake, thinking that the process will eventually become "bullet-proof", but I've found that this is not a substitute for peer reviews. Also, when it's possible to enforce a behavior through mechanical gates (scripts, tests), do it.

As AGENTS.md kept growing based on practical experience with the harness and models, it became unwieldy. That's how the idea of separating the process documentation into smaller, focused parts came about: AGENTS.md covers the philosophy and cross-cutting concerns, while the playbooks describe how to carry out tasks in practice.

Each playbook has a quota (maximum number of words and number of lines) to try and prevent that the playbook grows in an uncontrolled fashion. However, this can be a double-edged sword; I experienced more than once that the agent decided to dumb down existing text (practically reducing it to caveman speak) to make room for additional information, instead of increasing the budget _when the increase was justified_.

Be specific about the target audience of the output (code and documentation). After I explained that the target audience are experienced NES developers, the kinds of code comments I expect (and those that are clearly redundant) follow quite naturally.

Watch out for agents that ignore the rules and insist on using WORKING_NOTES.md and DX_Systems.md as a dumping ground for pass diaries. (In an attempt to detect and reject this anomaly, I added a hard limit on the size/length of WORKING_NOTES.md.)

My favorite instruction to the agent when I want them to work without interruption until they have blown my token budget: "Keep making passes until you pass out!"

## Conclusions and future work

There you have it: A repeatable process for reliably reverse engineering
any NES game. If you do manage to run the process yourself, I'd love to hear about it. Which game did you pick, and how many passes did it take to reach gold standard? Were the outputs (code and documentation) easy to follow? Were you able to make a simple mod? Did your agent(s) produce any entries in `FRICTION.md`?

So far I've ran the process to completion on roughly 20 games. I intend to complete all first- and second-party games (including those that use the MMC3 chip), then move on to other development houses (like Konami, Capcom, Sunsoft); it will be very interesting to see how their implementations differ from Nintendo's. I will keep improving the harness and related tooling every time an opportunity arises, and look into ways to automate this part as well. I want to make it easy to run the process and capture results in a way that makes it possible to compare separate runs (e.g., with different models and reasoning levels, with and without peer reviews, with and without access to the game manual).

## Appendix A: BIT overlay trick

Some games, such as Pinball, use a BIT instruction overlay trick in place of branch instructions. The NESrev disassembler doesn't yet detect this pattern; it unconditionally decodes the BIT instruction with its 16-bit operand (address), when the "tricky" operand is actually a valid 2-byte instruction. Here's what code using this trick can look like (after NESrev's output has been "repaired"):

```
Handler1:
    LDX #0
    .DB $2C   ; BIT absolute (skip next 2 bytes)
Handler2:
    LDX #$04  ; It's an instruction, but also a BIT operand
    .DB $2C   ; BIT absolute (skip next 2 bytes)
Handler3:
    LDX #$08  ; It's an instruction, but also a BIT operand
    ; At this point, X is 0 or 4 or 8, depending on the entrypoint
```
Effectively, the BIT instruction skips the instruction that is encoded in its 16-bit operand, whereas that "interior instruction" can at the same time be the target of a branch instruction. This is not without side-effects, as the BIT instruction actually reads memory (the interior instruction interpreted as an address) and updates status flags. Pretty evil trick, just to save one byte over each branch instruction (at the expense of more CPU cycles).

The BIT trick is documented in the playbooks, so that operators can know how to detect it and fix up the code.
