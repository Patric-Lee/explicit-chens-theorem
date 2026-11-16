import PlattPointSubsetKernel
import PlattPointPackets.S6B000270
import PlattPointPackets.S6B000271
import PlattPointPackets.S6B000272
import PlattPointPackets.S6B000273
import PlattPointPackets.S6B000274
import PlattPointPackets.S6B000275
import PlattPointPackets.S6B000276
import PlattPointPackets.S6B000277
import PlattPointPackets.S6B000278
import PlattPointPackets.S6B000279
import PlattPointPackets.S6B000280
import PlattPointPackets.S6B000281
import PlattPointPackets.S6B000282
import PlattPointPackets.S6B000283
import PlattPointPackets.S6B000284
import PlattPointPackets.S6B000285
import PlattGlobalGrid.S8B000084
namespace ChenEffective.PlattWindow.PointCovers.S8B000084
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000270.points ++ ChenEffective.PlattWindow.PointPackets.S6B000271.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000272.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000273.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000274.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000275.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000276.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000277.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000278.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000279.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000280.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000281.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000282.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000283.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000284.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000285.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000084.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000084.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000084
