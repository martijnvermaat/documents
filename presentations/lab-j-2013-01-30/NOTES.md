Open and Reproducible Scientific Programming
============================================

- Scientific findings should be:
  - Replicable (verify the method and result)
  - Reproducible (verify the result by other means)
  - Reusable (build on previous results)

- Publish data
  - "Authors must follow standards and practice for data deposition in
  publicly available resources including those created for gene sequences,
  microarray expression, structural studies, and similar kinds of
  data. Failure to comply with community standards may result in rejection."
  (PLOS ONE Publication Criteria, http://www.plosone.org/static/publication)
  - Publish variants
  - Use data standards (part of certain requirements the data publishing is
  subject to)
  (http://www.nature.com/nbt/journal/v28/n11/full/nbt1110-1181.html)

- Publish code
  - Computational science, results depend on software

- Incentives
  - "[Requiring that source code be made available upon publication] would
   bring disclosure and publication requirements for computer codes in line
   with other types of scientific data and materials"
  (http://www.sciencemag.org/content/336/6078/159.full)
  - "Although it is now accepted that data should be made available on
  request, the current regulations regarding the availability of software
  are inconsistent. We argue that, with some exceptions, anything less than
  the release of source programs is intolerable for results that depend on
  computation."
  (http://www.nature.com/nature/journal/v482/n7386/full/nature10836.html)
  - "Of the 20 most-cited journals in 2010 from all fields of science (15), only
  three (16–18) (including Science) have editorial policies requiring
  availability of computer source code upon publication. This stands in stark
  contrast to near-universal agreement among the 20 on policies regarding
  availability of data and other enabling materials."
  (http://www.sciencemag.org/content/336/6078/159.full)
  - "To address the growing complexity of data and analyses, Science is
  extending our data access requirement listed above to include computer
  codes involved in the creation or analysis of data."
  http://www.sciencemag.org/content/331/6018/649.full
  - "Nature does not require authors to make code available, but we do
  expect a description detailed enough to allow others to write their
  own code to do a similar analysis."
  (http://www.nature.com/nature/journal/v470/n7334/full/470305b.html)
  - "The editors of Bioinformatics encourage authors to make their source code
  available and, if possible, to provide access through an open source license
  (see http://www.opensource.org for examples). Authors should make every
  effort to use URLs that will remain stable. At the minimum, authors must
  provide one of: webserver, source code or binary."

- Software development is not research
  - "Time spent on software development that doesn't result in
  widely-recognized deliverables such as publications or grants is essentially
  time wasted, and will be inversely correlated with your chances of success
  as an academic."
  - Changing attitudes in academia to value software as much as (or more than)
  publications. It's all about reputation.
  - "This week, the National Science Foundation announced changes to its grant
  proposal guide (GPG). One of the changes is the acknowledgement of datasets,
  patents, software, and copyrights as citable products of research, eligible
  for inclusion in a researcher's biosketch."
  (http://www.galter.northwestern.edu/news/index.cfm/2012/10/9/Datasets-Software-Eligible-for-Listing-in-NSF-Biosketches)

- Good examples
  - "The 1000 Genomes Project, for example, a project to sequence and
  analyse more than a thousand genomes, has carefully detailed its
  workflows, and makes both its data and its procedures available for
  the world to see."
  (http://www.nature.com/nature/journal/v470/n7334/full/470305b.html)
  - "As part of the supplementary material for this paper, we have established a
  virtual machine instance of the software, using the code bundles from
  ftp.ebi.ac.uk/pub/databases/ensembl/encode/supplementary/, where each analysis
  program has been tested and run."
  "Where possible the VM enables complete reproduction of the analysis as it was
  performed to generate the figures, tables or other information."
  (http://scofield.bx.psu.edu/~dannon/encodevm/)

- Why not publish code
  - Someone will run with my idea -> claim territory
  - Ashamed to publish bad code -> don't be, write better code, CRAPL license
  - Algorithmic description is enough -> replication difficult, ambiguous descriptions, not reusable
  - Publishing oblicates you to support -> no it doesn't
  - Time, effort, money -> perfect and easy free options

- Reproducibility
  - http://www.sciencemag.org/content/334/6060/1226.full Reproducability in
  Computational Science
  - Not only for verification, also to regenerate lost data and to generate
  further data that "matches" the existing data
  - Required, any or all of the following:
    1. Same input data
    2. Same build tools and settings
    3. Same source code
    4. Same software settings
    5. Same OS and environment
    6. Same hardware
    Need provenance for this information.

- Computational analysis
  - Workflow systems
  - Web services
  - "We propose capturing and exchanging computational pipelines using
  complete digital representations of the entire computing environment
  needed to execute the pipeline."
  (http://www.nature.com/nbt/journal/v28/n11/full/nbt1110-1181.html)

- Research and source code
  - Integrate code with data, graphs, and article text
  - Literate programming (R)
  - IPython Notebook

- Write good code
  - Just as with publishing data, publishing source code could be subject to
    certain requirements
  - Follow best practices

- In practice
  - The ten commandments of scientific coding
  - Ten Simple Rules for the Open Development of Scientific Software
  - Best Practices for Scientiﬁc Computing
  - All have 10 commandments/rules/practices, but different
  - In all three: Don't reinvent the wheel (and collaborate)

- Things are changing
  - Science Code Manifesto http://sciencecodemanifesto.org/
  - Bioinformatics Testing Consortium http://biotest.cgrb.oregonstate.edu/
  - Software Carpentry http://software-carpentry.org/
  - Programming course


Sources
-------

overlyhonestmethods https://twitter.com/ianholmes/status/288689712636493824
wtfm http://www.osnews.com/story/19266/WTFs_m


Computational research
----------------------

Publish the original raw data online and make it freely available for
download.

Make the code base open source and available online for download.

CRAPL license.

Allows others to perform their own analyses on the same data, which
increases the level of confidence in the validity of your own
analyses.

Additionally, making your code open source makes it possible for the
code and procedure to be reviewed by your peers. Often such reviews
lead to the discovery of flaws or of the possibility for additional
optimization and improvement. Most importantly, it allows other
researchers to improve on your methods, without having to implement
everything that you have already done from scratch. It very greatly
accelerates the pace of research when researches can focus on just
improvements and not on reinventing the wheel.

myExperiment can be used to share workflows.

Some prestigious journals, including Science, have even started to
demand of authors to provide the source code for simulation software
used in publications to readers upon request.

Authors must follow standards and practice for data deposition in
publicly available resources (from PLOS ONE publication criteria). But
this is for data, not source code.


Integrate code with data, graphs, and article text
--------------------------------------------------

Literate programming (R).

IPython Notebook.


Source code disclosure policy
-----------------------------

http://www.sciencemag.org/content/336/6078/159.full

Achieving this would bring disclosure and publication requirements for
computer codes in line with other types of scientific data and
materials.

It has been done before for data disclosure, pretty successfully.

http://www.nature.com/nature/journal/v482/n7386/full/nature10836.html

http://www.sciencemag.org/content/331/6018/649.full

"To address the growing complexity of data and analyses, Science is
extending our data access requirement listed above to include computer
codes involved in the creation or analysis of data."

http://www.nature.com/nature/journal/v470/n7334/full/470305b.html

"Nature does not require authors to make code available, but we do
expect a description detailed enough to allow others to write their
own code to do a similar analysis."

"The 1000 Genomes Project, for example, a project to sequence and
analyse more than a thousand genomes, has carefully detailed its
workflows, and makes both its data and its procedures available for
the world to see."

Code descriptions are ambiguous.

http://scofield.bx.psu.edu/~dannon/encodevm/

As part of the supplementary material for this paper, we have established a
virtual machine instance of the software, using the code bundles from
ftp.ebi.ac.uk/pub/databases/ensembl/encode/supplementary/, where each analysis
program has been tested and run.

Where possible the VM enables complete reproduction of the analysis as it was
performed to generate the figures, tables or other information.


Incentives for good software practices in academia
--------------------------------------------------

http://www.bendmorris.com/2012/12/what-incentives-are-there-to-maintain.html

Time spent on software development that doesn't result in widely-recognized
deliverables such as publications or grants is essentially time wasted, and
will be inversely correlated with your chances of success as an academic.

Changing attitudes in academia to value software as much as (or more than)
publications. It's all about reputation.

http://www.galter.northwestern.edu/news/index.cfm/2012/10/9/Datasets-Software-Eligible-for-Listing-in-NSF-Biosketches

This week, the National Science Foundation announced changes to its grant
proposal guide (GPG). One of the changes is the acknowledgement of datasets,
patents, software, and copyrights as citable products of research, eligible
for inclusion in a researcher's biosketch.

The editors of Bioinformatics encourage authors to make their source code
available and, if possible, to provide access through an open source license
(see http://www.opensource.org for examples). Authors should make every effort
to use URLs that will remain stable. At the minimum, authors must provide one
of: webserver, source code or binary.

http://www.slideshare.net/jandot/b-temperton-the-bioinformatics-testing-consortium
http://biotest.cgrb.oregonstate.edu/
http://bytesizebio.net/wp-content/uploads/2012/08/btc.png
https://twitter.com/luispedrocoelho/status/238632048313647104


In silico research in the era of cloud computing
------------------------------------------------

http://www.nature.com/nbt/journal/v28/n11/full/nbt1110-1181.html

Existing software applications have not become established solutions
to the problem of computational reproducibility:

1. Efforts are not rewarded by the current academic research and
funding environment.

2. Commercial software vendors tend to protect their markets through
proprietary formats and interfaces.

3. Investigators naturally tend to want to own and control their
research tools.

4. Even the most generalized software will not be able to meet the
needs of every researcher in a field.

5. The need to derive and publish results as quickly as possible
precludes the often slower standards-based development path.

Given these realities, we propose capturing and exchanging
computational pipelines using complete digital representations of the
entire computing environment needed to execute the pipeline.

-> Use cloud.


Data standards
--------------

http://online.liebertpub.com/doi/abs/10.1089/omi.2006.10.94

Please use data standards. Easier with commandment 3.


Reproducability
---------------

http://conferences.ncl.ac.uk/sciprog/Presentations/9_A1_SSI-Reproducibility.pdf

1. Regenerate lost data
2. Generate further data that "matches" the existing data
3. Verify correctness

Required, any or all of the following:

1. Same input data
2. Same build tools and settings
3. Same source code
4. Same software settings
5. Same OS and environment
6. Same hardware

Need provenance for this information.

http://www.sciencemag.org/content/334/6060/1226.full

Anyone doing any computing in their research should publish their
code. It does not have to be clean or beautiful (13), it just needs to
be available. Even without the corresponding data, code can be very
informative and can be used to check for problems as well as quickly
translate ideas. Journal editors and reviewers should demand this so
that it becomes routine. Publishing code is something we can do now
for almost no additional cost. Free code repositories already exist
[for example, GitHub (http://github.com) and SourceForge (http://sourceforge.net)],
and at a minimum, code can be published in supporting online
material. The next step would be to publish a cleaned-up version of
the code along with the data sets in a durable nonproprietary format.


Python
------

http://nbviewer.ipython.org/urls/raw.github.com/jrjohansson/scientific-python-lectures/master/Lecture-0-Scientific-Computing-with-Python.ipynb
http://jrjohansson.github.com/

IPython Notebook.


The Ten Commandments of Scientific Coding
-----------------------------------------

1. Thou shall use version control.
   - Keeping track (files, versions, changes)
   - Collaborating
   Reproducability, go back to computation of previous results.
   Source code, input data sets, instructions, Makefile, result data
   sets.
2. Thou shall comment thy code.
3. Thou shall use existing libraries whenever possible.
   This can conflict with commandment 1.
   Also see commandment 9.
4. Thou shall try to unit test.
   Regression testing.
   Automated.
5. Thou shall not make up statistical procedures.
6. Thou shall read code other than thy own.
   Tunnel vision.
   Researchers also read literature.
7. Thou shall write documentation.
   For users and for developers.
8. Thou shall beware of floating point issues.
9. Thou shall write modular code.
   Extreme would be Taverna.
   Re-use.
10. Thou shall follow coding standards.


Ten Simple Rules for the Open Development of Scientific Software
----------------------------------------------------------------

1. Don't Reinvent the Wheel
2. Code Well
3. Be Your Own User
4. Be Transparent
5. Be Simple
6. Don't Be a Perfectionist
7. Nurture and Grow Your Community
8. Promote Your Project
9. Find Sponsors
10. Science Counts


Best Practices for Scientiﬁc Computing
--------------------------------------

http://arxiv.org/abs/1210.0530

1. Write programs for people, not computers
   - People: users and developers
   - Consistent and predictable interface
   - Coding standards

2. Automate repetitive tasks
   - Tools to automate workflows
   - Store commands in a script

3. Use the computer to record history

4. Make incremental changes

5. Use version control
   - Everything that has been created manually

6. Don't repeat yourself (or others)
   - Modularize instead of copy/paste
   - Have a single representation for every piece of data
   - Re-use instead of rewrite

7. Plan for mistakes
   - Use assertions
   - Have unit tests
   - Turn bugs into test cases

8. Optimize software only after it works correctly

9. Document design and purpose, not mechanics
   - Interfaces and reasons, not implementations
   - Refactor rather than explain
   - Embed the documentation for a piece of software in that software

10. Collaborate
   - Use code review and pair programming
   - Pre-merge code reviews (often found to be intrusive)
   - Tools for issue tracking

"A large body of research has shown that code reviews are the most
cost-effective way of finding bugs in code"

"recent high-proﬁle retractions, technical comments, and corrections because
of errors in computational methods include papers in Science [6], PNAS [39],
the Journal of Molecular Biology [5], Ecology Letters [37, 8], the Journal of
Mammalogy [33], and Hypertension [26]."


Where to host data and code
---------------------------

http://gettinggeneticsdone.blogspot.nl/2013/01/stop-hosting-data-and-code-on-your-lab.html

Schultheiss, Sebastian J., et al. "Persistence and availability of web
services in computational biology." PLoS one 6.9 (2011): e24914.

In a survey of nearly 1000 web services published in the Nucleic Acids Web
Server Issue between 2003 and 2009:
- Only 72% were still available at the published address.
- The authors could not test the functionality for 33% because there was no
  example data, and 13% no longer worked as expected.
- The authors could only confirm positive functionality for 45%.
- Only 274 of the 872 corresponding authors answered an email.
- Of these 78% said a service was developed by a student or temporary
  researcher, and many had no plan for maintenance after the researcher had
  moved on to a permanent position.

Wren, Jonathan D. "404 not found: the stability and persistence of URLs
published in MEDLINE." Bioinformatics 20.5 (2004): 668-672.

- Of 1630 URLs identified in Pubmed abstracts only 63% were consistently
  available.
- That rate was far worse for anonymous login FTP sites (33%).


Software Carpentry
------------------

http://software-carpentry.org/

http://software-carpentry.org/files/papers/aranda-assessment-2012-07.pdf

"Most scientists are self-taught programmers, they have fundamental weaknesses
in their software development expertise, and these weaknesses affect their
ability to answer their research questions."


Links
-----

http://www.nature.com/nature/journal/v482/n7386/full/nature10836.html
http://www.runmycode.org/data/MetaSite/upload/nature10836.pdf
http://simplystatistics.org/2013/01/23/statisticians-and-computer-scientists-if-there-is-no-code-there-is-no-paper/
http://simplystatistics.org/2012/08/17/interview-with-c-titus-brown-computational-biologist/
http://andrewgelman.com/2012/02/meta-analysis-game-theory-and-incentives-to-do-replicable-research/
http://www.johndcook.com/blog/2010/10/19/buggy-simulation-code-is-biased/
http://arxiv.org/abs/1010.1092
http://blog.revolutionanalytics.com/2009/08/because-its-friday-correcting-the-academic-record.html
http://www.nature.com/news/2010/101013/full/467775a.html
http://muse.jhu.edu/login?auth=0&type=summary&url=/journals/journal_of_money_credit_and_banking/v038/38.4mccullough.pdf
https://gist.github.com/3311557
http://news.ycombinator.com/item?id=4815399
http://instacode.linology.info/
http://matt.might.net/articles/crapl/
https://speakerdeck.com/ptomato/open-and-reproducible-scientific-programming
http://www.ncbi.nlm.nih.gov/pubmed/16646837
http://software-carpentry.org/
http://manu.sporny.org/2011/public-domain-genome/
