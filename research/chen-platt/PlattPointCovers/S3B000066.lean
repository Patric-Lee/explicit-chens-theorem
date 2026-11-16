import PlattPointSubsetKernel
import PlattPointPackets.S1B000048
import PlattPointPackets.S1B000049
import PlattGlobalGrid.S3B000066
namespace ChenEffective.PlattWindow.PointCovers.S3B000066
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (ChenEffective.PlattWindow.PointPackets.S1B000048.points ++ ChenEffective.PlattWindow.PointPackets.S1B000049.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S3B000066.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S3B000066.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S3B000066
