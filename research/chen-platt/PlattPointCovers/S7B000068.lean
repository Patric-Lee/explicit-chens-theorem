import PlattPointSubsetKernel
import PlattPointPackets.S3B000002
import PlattPointPackets.S3B000003
import PlattPointPackets.S3B000004
import PlattPointPackets.S3B000005
import PlattPointPackets.S3B000006
import PlattPointPackets.S3B000007
import PlattGlobalGrid.S7B000068
namespace ChenEffective.PlattWindow.PointCovers.S7B000068
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S3B000002.points ++ ChenEffective.PlattWindow.PointPackets.S3B000003.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000004.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000005.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000006.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000007.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000068.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000068.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000068
