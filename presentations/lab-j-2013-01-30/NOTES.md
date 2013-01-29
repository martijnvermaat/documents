The Ten Commandments of Scientific Coding
=========================================

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


1. Thou shall use version control.
----------------------------------

Reproducability, go back to computation of previous results.

Source code, input data sets, instructions, Makefile, result data
sets.


2. Thou shall comment thy code.
-------------------------------


3. Thou shall use existing libraries whenever possible.
-------------------------------------------------------

This can conflict with commandment 1.


4. Thou shall try to unit test.
-------------------------------

Regression testing.
Automated.


5. Thou shall not make up statistical procedures.
-------------------------------------------------


6. Thou shall read code other than thy own.
-------------------------------------------


7. Thou shall write documentation.
----------------------------------


8. Thou shall beware of floating point issues.
----------------------------------------------


9. Thou shall write modular code.
---------------------------------

Extreme would be Taverna.


10. Thou shall follow coding standards.
---------------------------------------




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
