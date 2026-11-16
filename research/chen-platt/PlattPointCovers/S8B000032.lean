import PlattPointSubsetKernel
import PlattPointPackets.S4B000268
import PlattPointPackets.S4B000269
import PlattPointPackets.S4B000270
import PlattPointPackets.S4B000271
import PlattPointPackets.S4B000272
import PlattPointPackets.S4B000273
import PlattPointPackets.S4B000274
import PlattPointPackets.S4B000275
import PlattPointPackets.S4B000276
import PlattPointPackets.S4B000277
import PlattPointPackets.S4B000278
import PlattGlobalGrid.S8B000032
namespace ChenEffective.PlattWindow.PointCovers.S8B000032
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((ChenEffective.PlattWindow.PointPackets.S4B000268.points ++ ChenEffective.PlattWindow.PointPackets.S4B000269.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000270.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000271.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000272.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000273.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000274.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000275.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000276.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000277.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000278.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000032.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000032.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000032
