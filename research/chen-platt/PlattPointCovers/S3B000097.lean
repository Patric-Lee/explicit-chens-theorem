import PlattPointSubsetKernel
import PlattPointPackets.S1B000056
import PlattPointPackets.S1B000057
import PlattGlobalGrid.S3B000097
namespace ChenEffective.PlattWindow.PointCovers.S3B000097
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (ChenEffective.PlattWindow.PointPackets.S1B000056.points ++ ChenEffective.PlattWindow.PointPackets.S1B000057.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S3B000097.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S3B000097.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S3B000097
