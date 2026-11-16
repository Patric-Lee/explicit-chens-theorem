import PlattPointSubsetKernel
import PlattPointPackets.S3B000276
import PlattPointPackets.S3B000277
import PlattPointPackets.S3B000278
import PlattPointPackets.S3B000279
import PlattPointPackets.S3B000280
import PlattPointPackets.S3B000281
import PlattPointPackets.S3B000282
import PlattPointPackets.S3B000283
import PlattGlobalGrid.S7B000113
namespace ChenEffective.PlattWindow.PointCovers.S7B000113
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((ChenEffective.PlattWindow.PointPackets.S3B000276.points ++ ChenEffective.PlattWindow.PointPackets.S3B000277.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000278.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000279.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000280.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000281.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000282.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000283.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000113.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000113.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000113
