import PlattPointSubsetKernel
import PlattPointPackets.S1B000049
import PlattPointPackets.S1B000050
import PlattGlobalGrid.S3B000070
namespace ChenEffective.PlattWindow.PointCovers.S3B000070
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (ChenEffective.PlattWindow.PointPackets.S1B000049.points ++ ChenEffective.PlattWindow.PointPackets.S1B000050.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S3B000070.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S3B000070.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S3B000070
