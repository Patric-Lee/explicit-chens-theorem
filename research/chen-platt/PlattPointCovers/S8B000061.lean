import PlattPointSubsetKernel
import PlattPointPackets.S5B000273
import PlattPointPackets.S5B000274
import PlattPointPackets.S5B000275
import PlattPointPackets.S5B000276
import PlattPointPackets.S5B000277
import PlattPointPackets.S5B000278
import PlattPointPackets.S5B000279
import PlattPointPackets.S5B000280
import PlattPointPackets.S5B000281
import PlattPointPackets.S5B000282
import PlattPointPackets.S5B000283
import PlattPointPackets.S5B000284
import PlattPointPackets.S5B000285
import PlattPointPackets.S5B000286
import PlattGlobalGrid.S8B000061
namespace ChenEffective.PlattWindow.PointCovers.S8B000061
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((ChenEffective.PlattWindow.PointPackets.S5B000273.points ++ ChenEffective.PlattWindow.PointPackets.S5B000274.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000275.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000276.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000277.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000278.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000279.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000280.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000281.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000282.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000283.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000284.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000285.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000286.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000061.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000061.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000061
