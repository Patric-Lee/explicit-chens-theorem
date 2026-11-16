import PlattPointSubsetKernel
import PlattPointPackets.S3B000173
import PlattPointPackets.S3B000174
import PlattPointPackets.S3B000175
import PlattPointPackets.S3B000176
import PlattPointPackets.S3B000177
import PlattPointPackets.S3B000178
import PlattPointPackets.S3B000179
import PlattPointPackets.S3B000180
import PlattGlobalGrid.S7B000098
namespace ChenEffective.PlattWindow.PointCovers.S7B000098
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((ChenEffective.PlattWindow.PointPackets.S3B000173.points ++ ChenEffective.PlattWindow.PointPackets.S3B000174.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000175.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000176.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000177.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000178.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000179.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000180.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000098.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000098.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000098
