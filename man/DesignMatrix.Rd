\name{DesignMatrix}
\alias{DesignMatrix}
\title{DesignMatrix}

\description{
 Returns hierarchical model design matrix
}

\usage{
DesignMatrix(var, suffconfigs, dim, SubsetCoding = "Automatic", MakeSubsets=TRUE)
}

\arguments{
  \item{var}{character or numeric vector containing variables}
  \item{suffconfigs}{subvector or list of subvectors of \code{var} indicating the sufficient configurations or highest order interactions in model}
  \item{dim}{numeric vector indicating the dimension of \code{var} (must be same length as \code{var})}
  \item{SubsetCoding}{allows a (character) type or a matrix to be assigned to variables for each element of \code{suffconfigs}}, see examples
  \item{MakeSubsets}{boolean, indicates whether or not to use subsets of \code{suffconfigs} (used as option in \code{MarginaMatrix})}
}

\details{
The design matrix for a model \eqn{\mu_{ij}=\alpha+\beta_{i}+\gamma_j}{mu_ij = alpha + beta_i + gamma_j}, 
where \eqn{i}{i} and \eqn{j}{j} each have three possible values, would be:
\code{Designmatrix(c(1,2),list(c(1),c(2)),c(3,3))}.
For readability, the use of characters is recommended for variable names, e.g.,
\code{Designmatrix(c("A","B"),list(c("A"),c("B")),c(3,3))}.
The probability vector is assumed to be a vectorized form of the probabilities in a table, 
such that the last variable changes value fastest, then the before last variable, etc. 
For example, the cells of a \eqn{2 \times 3}{2 x 3} table are arranged in vector form as (11,12,13,21,22,23).
To achieve this, the appropriate way to vectorize a data frame \code{dat} is using \code{c(t(ftable(dat)))}.


The optional argument \code{SubsetCoding} is useful for e.g.\ specifying various regression models,
a linear by nominal model, grouping categories of a variable, or
omitting a category. \code{SubsetCoding} has default value
\code{"Automatic"}, which is the same as the value \code{"Nominal"}.
Other options are \code{"Linear"}, \code{"Quadratic"},
\code{"Cubic"}, \code{"Quartic"}, \code{"Quintic"}, \code{"Identity"}.\\
The command \code{ConstraintMatrix} is often more useful than \code{DesignMatrix} for specification of models
for use in \code{SampleStatistics}, \code{ModelStatistics} or \code{MarginalModelFit}.
}

\value{
 matrix
}

\references{
  Bergsma, W. P. (1997).
  \emph{Marginal models for categorical data}.
  Tilburg, The Netherlands: Tilburg University Press.
  \url{http://stats.lse.ac.uk/bergsma/pdf/bergsma_phdthesis.pdf}

  Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).
  Marginal models for dependent, clustered, and longitudunal categorical data.
  Berlin: Springer.
}


\author{
 W. P. Bergsma \email{w.p.bergsma@lse.ac.uk}
}

\seealso{
\code{\link{ConstraintMatrix}}, \code{\link{MarginalMatrix}}, \code{\link{DirectSum}}
}

\examples{

# Design matrix for independence model
var <- c("A","B")
suffconfigs <- list(c("A"),c("B"))
dim <- c(3, 3)
DesignMatrix(var,suffconfigs,dim)
# notation in one line
DesignMatrix(c("A","B"),list(c("A"),c("B")),c(3,3))


# Design matrix for saturated model, two short specifications giving same result
DesignMatrix(c("A","B"),c("A","B"),c(3,3))
DesignMatrix(c("A","B"),list(c("A","B")),c(3,3))


# Design matrix for univariate quadratic regression model
var <- c("A")
suffconfigs <- c("A")
dim <- c(5)
DesignMatrix(var,suffconfigs,dim,SubsetCoding=list(c("A"),"Quadratic"))
# notation in one line
DesignMatrix(c("A"),c("A"),c(5),SubsetCoding=list(c("A"),"Quadratic"))


# Design matrix for linear by nominal model, various methods:
# simplest method which assumes equidistant centered scores:
DesignMatrix(
 var = c("A","B"),
 suffconfigs = c("A", "B"),
 dim = c(3,3),
 SubsetCoding = list(c("A","B"),list("Linear","Nominal")))
# alternative specification with same result as above:
DesignMatrix(
 var = c("A", "B"),
 suffconfigs = c("A", "B"),
 dim = c(3, 3),
 SubsetCoding = list(c("A","B"),list(rbind(c(-1,0,1)),rbind(c(1,0,0),c(0,1,0)))))
# specifying your own category scores
scores <- c(1,2,5);
DesignMatrix(
 var = c("A","B"),
 suffconfigs = c("A","B"),
 dim = c(3, 3),
 SubsetCoding = list(c("A","B"), list(rbind(scores), "Nominal")))

# Design matrix for nominal by nominal model, equating parameters 
# of last two categories of second variable:
DesignMatrix(
 var = c("A", "B"),
 suffconfigs = c("A","B"),
 dim = c(3,3),
 SubsetCoding = list(c("A", "B"), list("Nominal", rbind(c(1, 0, 0), c(0, 1, 1)))))
}

\keyword{univar}
