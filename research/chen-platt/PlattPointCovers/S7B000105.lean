import PlattPointSubsetKernel
import PlattPointPackets.S3B000220
import PlattPointPackets.S3B000221
import PlattPointPackets.S3B000222
import PlattPointPackets.S3B000223
import PlattPointPackets.S3B000224
import PlattPointPackets.S3B000225
import PlattPointPackets.S3B000226
import PlattPointPackets.S3B000227
import PlattGlobalGrid.S7B000105
namespace ChenEffective.PlattWindow.PointCovers.S7B000105
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((ChenEffective.PlattWindow.PointPackets.S3B000220.points ++ ChenEffective.PlattWindow.PointPackets.S3B000221.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000222.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000223.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000224.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000225.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000226.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000227.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000105.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000105.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000105
