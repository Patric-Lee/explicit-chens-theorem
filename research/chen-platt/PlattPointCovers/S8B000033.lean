import PlattPointSubsetKernel
import PlattPointPackets.S4B000278
import PlattPointPackets.S4B000279
import PlattPointPackets.S4B000280
import PlattPointPackets.S4B000281
import PlattPointPackets.S4B000282
import PlattPointPackets.S4B000283
import PlattPointPackets.S4B000284
import PlattPointPackets.S4B000285
import PlattPointPackets.S4B000286
import PlattPointPackets.S4B000287
import PlattPointPackets.S4B000288
import PlattGlobalGrid.S8B000033
namespace ChenEffective.PlattWindow.PointCovers.S8B000033
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((ChenEffective.PlattWindow.PointPackets.S4B000278.points ++ ChenEffective.PlattWindow.PointPackets.S4B000279.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000280.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000281.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000282.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000283.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000284.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000285.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000286.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000287.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000288.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000033.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000033.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000033
