import PlattPointSubsetKernel
import PlattPointPackets.S3B000007
import PlattPointPackets.S3B000008
import PlattPointPackets.S3B000009
import PlattPointPackets.S3B000010
import PlattPointPackets.S3B000011
import PlattPointPackets.S3B000012
import PlattGlobalGrid.S7B000069
namespace ChenEffective.PlattWindow.PointCovers.S7B000069
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S3B000007.points ++ ChenEffective.PlattWindow.PointPackets.S3B000008.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000009.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000010.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000011.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000012.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000069.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000069.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000069
