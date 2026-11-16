import PlattPointSubsetKernel
import PlattPointPackets.S3B000305
import PlattPointPackets.S3B000306
import PlattPointPackets.S3B000307
import PlattGlobalGrid.S7B000117
namespace ChenEffective.PlattWindow.PointCovers.S7B000117
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S3B000305.points ++ ChenEffective.PlattWindow.PointPackets.S3B000306.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000307.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000117.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000117.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000117
