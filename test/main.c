#include <stdio.h>
#include "./../src/lua.h"
#include "./../src/lauxlib.h"
#include "./../src/ltable.h"

//extern unsigned int computesizes(unsigned int nums[], unsigned int *pna);

void executeLua()
{
	lua_State * lstate = luaL_newstate();
	luaL_openlibs(lstate);
	if (luaL_loadfile(lstate, "test.lua") || lua_pcall(lstate, 0, 0, 0))
	{
		printf("error:  %s\n", lua_tostring(lstate, -1));
	}
	lua_close(lstate);
}

int main()
{
	int nums[] = { 1 };
	int a = 2;

	executeLua();

	system("pause");

	return 0;
}