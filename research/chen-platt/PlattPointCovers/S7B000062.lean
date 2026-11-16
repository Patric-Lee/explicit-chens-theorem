import PlattPointSubsetKernel
import PlattPointPackets.S2B000285
import PlattPointPackets.S2B000286
import PlattPointPackets.S2B000287
import PlattPointPackets.S2B000288
import PlattPointPackets.S2B000289
import PlattPointPackets.S2B000290
import PlattGlobalGrid.S7B000062
namespace ChenEffective.PlattWindow.PointCovers.S7B000062
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S2B000285.points ++ ChenEffective.PlattWindow.PointPackets.S2B000286.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000287.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000288.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000289.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000290.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000062.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000062.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000062
