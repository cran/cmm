%to do: examples

\name{ModelStatistics}
\alias{ModelStatistics}
\title{ModelStatistics}

\description{If fitted frequencies under a model have been calculated, this procedure can be used to give sample values,
fitted values, estimated standard errors, z-scores and adjusted residuals of one or more coefficients.
}

\usage{ModelStatistics(dat, fitfreq, model, coeff, CoefficientDimensions = "Automatic",
    Labels = "Automatic", Method = "ML", ShowCoefficients = TRUE, ShowParameters = FALSE, 
    ParameterCoding = "Effect", ShowCorrelations = FALSE, Title = "")}

\arguments{
\item{dat}{observed data as a list of frequencies or as a data frame}
\item{fitfreq}{vector of fitted frequencies for each cell of full table (including latent variables, if any)}
\item{model}{list specified eg as \code{list(bt,coeff,at)}}
\item{coeff}{list of coefficients, can be obtained using \code{\link{SpecifyCoefficient}}}
\item{CoefficientDimensions}{numeric vector of dimensions of the table in which the coefficient vector is to be arranged}
\item{Labels}{list of characters or numbers indicating labels for dimensions of table in which the coefficient vector is to be arranged}
\item{ShowCoefficients}{boolean, indicating whether or not the coefficients are to be displayed}
\item{ShowParameters}{boolean, indicating whether or not the parameters (computed from the coefficients) are to be displayed}
\item{Method}{character, choice of "ML" for maximum likelihood or "GSK" for the GSK method}
\item{ParameterCoding}{Coding to be used for parameters, choice of \code{"Effect"}, \code{"Dummy"} and  \code{"Polynomial"}}
\item{ShowCorrelations}{boolean, indicating whether or not to show the correlation matrix for the estimated coefficients}
\item{Title}{title of computation to appear at top of screen output}
}

\details{
The data can be a data frame or vector of frequencies. \code{MarginalModelFit} converts a data frame \code{dat} using \code{c(t(ftable(dat)))}.

For \code{ParameterCoding}, the default for \code{"Dummy"}
is that the first cell in the table is the reference cell. Cell
\eqn{(i,j,k,...)}{(i, j, k, ...)} can be made reference cell using
\code{list("Dummy",c(i,j,k,...))}. For \code{"Polynomial"} the
default is to use centralized scores based on equidistant (distance
1) linear scores, for example, if for \eqn{i=1,2,3,4},
\eqn{\mu_i=\alpha+q_i\beta+r_i\gamma+s_i\delta}{mu_i = alpha + q_i beta + r_i gamma + s_i delta} 
where \eqn{\beta}{beta} is a quadratic, \eqn{\gamma}{gamma} a cubic and \eqn{\delta}{delta} a 
quartic effect, then \eqn{q_i}{q_i} takes the values \eqn{(-1.5,-.5,.5,1.5)}{(-1.5, -.5, .5, 1.5)}, 
\eqn{r_i}{r_i} takes the values \eqn{(1,-1,-1,1)}{(1, -1, -1, 1)} 
(centralized squares of the \eqn{q_i}{q_i}), and \eqn{s_i}{s_i} takes the values 
\eqn{(-3.375,-.125,.125,3.375)}{(-3.375, -.125, .125, 3.375)} (cubes of the \eqn{q_i}{q_i}).}

\value{ A subset of the output of \code{MarginalModelFit}. }

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

\seealso{ \code{\link{ModelStatistics}},
\code{\link{MarginalModelFit}}}

\examples{

# Below an example where ModelStatistics can be used to get output for coefficients 
# not given by MarginalModelFit 

# Marginal homogeneity (MH) in a 3x3 table AB
# Note that MH is equivalent to independence in the 2x3 table of marginals IR, in which the 
# row with I=1 gives the A marginal, and the row with I=2 gives the B marginal 
n <- 1 : 9
at <- MarginalMatrix(c("A", "B"), list(c("A"), c("B")), c(3,3))
bt <- ConstraintMatrix(c("I", "R"), list(c("I"), c("R")), c(2,3))
model <- list( bt, "log", at)

#The "coefficients" for the model are the log marginal probabilities for table IR
fit <- MarginalModelFit(dat = n, model = model, 
 CoefficientDimensions = c(2, 3), Labels = c("I", "R"))

#to get output for the marginal probabilities, ModelStatistics can be used as follows
spec <-  SpecifyCoefficient("ConditionalProbabilities",list(c("I","R"),c("I"),c(2,3)))
coeff <- list(spec, at)
stats <- ModelStatistics(dat = n, fitfreq = fit$FittedFrequencies, 
 model = model, coeff = coeff, CoefficientDimensions = c(2, 3),
 Labels = c("I", "R"))
}

\keyword{univar}
