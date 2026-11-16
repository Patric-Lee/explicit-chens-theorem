import PlattPointSubsetKernel
import PlattPointPackets.S3B000186
import PlattPointPackets.S3B000187
import PlattPointPackets.S3B000188
import PlattPointPackets.S3B000189
import PlattPointPackets.S3B000190
import PlattPointPackets.S3B000191
import PlattPointPackets.S3B000192
import PlattPointPackets.S3B000193
import PlattGlobalGrid.S7B000100
namespace ChenEffective.PlattWindow.PointCovers.S7B000100
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((ChenEffective.PlattWindow.PointPackets.S3B000186.points ++ ChenEffective.PlattWindow.PointPackets.S3B000187.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000188.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000189.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000190.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000191.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000192.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000193.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000100.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000100.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000100
